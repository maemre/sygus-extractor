use clap::Parser;
use serde::Serialize;
use serde_derive::Serialize;
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use sygus_parser::ast::*;

#[derive(Debug, Parser)]
#[command(version, about, long_about = None)]
struct Args {
    sygus_file: PathBuf,
}

/// Sorts allowed in string grammars
#[derive(Serialize, Debug, PartialEq, Eq)]
enum Sort {
    String,
    Int,
    Bool,
}

/// Which rules are allowed for each sort
#[derive(Serialize, Default)]
struct Rules {
    string: Vec<String>,
    int: Vec<String>,
    bool: Vec<String>,
}

/// Which variables are allowed for each sort
#[derive(Serialize, Default)]
struct Vars {
    string: Vec<String>,
    int: Vec<String>,
    bool: Vec<String>,
}
/// Which literals are allowed for each sort
#[derive(Serialize, Default)]
struct Literals {
    string: Vec<String>,
    int: Vec<i64>,
    bool: Vec<bool>,
}

/// A synthesis problem
#[derive(Serialize)]
struct Problem {
    name: String,
    start: Sort,
    args: Vars,
    literals: Literals,
    rules: Rules,
    examples: Vec<(Vec<String>, String)>,
}

fn main() {
    let args = Args::parse();

    let text = fs::read_to_string(&args.sygus_file).expect("could not read the sygus file");

    let sygus_file = SyGuSFile::from_str(&text).unwrap();

    let mut name = String::from("");
    let mut rules = Rules::default();
    let mut start: Option<Sort> = None;
    let mut fun_args = Vars::default();
    let mut examples = Vec::<(Vec<String>, String)>::new();
    let mut has_seen_synth_fun = false;
    let mut function_name = String::new();
    let eq = Identifier::Symbol("=".to_string());
    let mut literals = Literals::default();

    let supported_ops: HashMap<&str, String> = HashMap::from([
        // (),
        ("str.++", "append".to_owned()),
        ("str.replace", "replace".to_owned()),
        ("str.at", "at".to_owned()),
        ("int.to.str", "int_to_str".to_owned()),
        ("str.substr", "substr".to_owned()),
        ("+", "+".to_owned()),
        ("-", "-".to_owned()),
        ("str.len", "len".to_owned()),
        ("str.to.int", "str_to_int".to_owned()),
        ("str.indexof", "index_of".to_owned()),
        ("str.prefixof", "prefix_of".to_owned()),
        ("str.suffixof", "suffix_of".to_owned()),
        ("str.contains", "contains".to_owned()),
        ("ite", "ite".to_owned()),
    ]);

    let parse_sort = |sort: sorts::Sort| match sort {
        sorts::Sort::Simple(Identifier::Symbol(sort)) => match sort.as_str() {
            "Int" => Sort::Int,
            "Bool" => Sort::Bool,
            "String" => Sort::String,
            _ => panic!("unsupported sort: {sort}"),
        },
        _ => panic!("unsupported sort: {sort}"),
    };

    for cmd in sygus_file.cmds {
        use SyGuSCmd::*;

        match cmd {
            Constraint(ref constraint @ SyGuSTerm::Application(ref eq_, ref args))
                if *eq_ == eq =>
            {
                let [SyGuSTerm::Application(f, inputs), SyGuSTerm::Literal(output)] =
                    args.as_slice()
                else {
                    panic!("unsupported equality constraint: {constraint}")
                };
                assert!(
                    inputs
                        .iter()
                        .all(|input| matches!(input, SyGuSTerm::Literal(_))),
                    "all function inputs in an example should be literals"
                );

                let inputs = inputs.iter().map(|input| {
                    if let SyGuSTerm::Literal(lit) = input {
                        lit
                    } else {
                        panic!("non-literal input in example: {input}")
                    }
                });

                if function_name == "" {
                    function_name = f.to_string();
                } else {
                    assert_eq!(function_name.as_str(), f.get_name());
                }

                // Pretty-print the output, stripping the quotes from strings
                let prettify = |literal: &Literal| match literal {
                    Literal::Numeral(n) => n.to_string(),
                    Literal::Bool(true) => "true".to_string(),
                    Literal::Bool(false) => "false".to_string(),
                    Literal::StringConst(s) => s[1..(s.len() - 1)].to_string(),
                    _ => panic!("unsupported literal: {output}"),
                };

                examples.push((inputs.map(prettify).collect(), prettify(output)));
            }
            Constraint(_) => panic!("unsupported constraint: {cmd}"),
            DeclareVar(name, sort) => eprintln!("ignoring universal var {name}: {sort}"),
            SynthFun(fun_name, args, sort, grammar_def) => {
                name = fun_name;
                if has_seen_synth_fun {
                    panic!("Problems with multiple synth-fun instances are not supported");
                }
                has_seen_synth_fun = true;
                for SortedVar { name, sort } in args {
                    match parse_sort(sort) {
                        Sort::Int => fun_args.int.push(name),
                        Sort::Bool => fun_args.bool.push(name),
                        Sort::String => fun_args.string.push(name),
                    }
                }

                start = Some(parse_sort(sort));

                let grammar_def =
                    grammar_def.expect("the synth-fun command must have a grammar attach");
                assert!(grammar_def.sorted_vars.is_empty());
                for rule_list in grammar_def.grouped_rule_lists {
                    let sort = parse_sort(rule_list.sort);
                    if rule_list.symbol == "Start" {
                        assert_eq!(Some(sort), start);
                        continue;
                    }

                    for term in rule_list.terms {
                        let SyGuSGTerm::SyGuSTerm(term) = term else {
                            panic!("variable/constant grammar terms are not supported")
                        };
                        match term.clone() {
                            SyGuSTerm::Identifier(identifier) => {
                                let name = identifier.to_string();
                                let is_var = match sort {
                                    Sort::String => fun_args.string.contains(&name),
                                    Sort::Int => fun_args.int.contains(&name),
                                    Sort::Bool => fun_args.bool.contains(&name),
                                };

                                if is_var {
                                    continue;
                                }

                                if name == "true" {
                                    assert_eq!(sort, Sort::Bool);
                                    literals.bool.push(true);
                                } else if name == "false" {
                                    assert_eq!(sort, Sort::Bool);
                                    literals.bool.push(false);
                                } else {
                                    unimplemented!("haven't implemented the identifier {name}");
                                }
                            }
                            SyGuSTerm::Literal(literal) => match literal {
                                Literal::Numeral(n) => literals.int.push(n as i64),
                                Literal::Bool(b) => literals.bool.push(b),
                                Literal::StringConst(s) => {
                                    literals.string.push(s[1..s.len() - 1].to_string())
                                }
                                _ => unreachable!(),
                            },
                            SyGuSTerm::Application(identifier, _) => {
                                if let Some(op) = supported_ops.get(identifier.get_name()) {
                                    match sort {
                                        Sort::String => rules.string.push(op.clone()),
                                        Sort::Int => rules.int.push(op.clone()),
                                        Sort::Bool => rules.bool.push(op.clone()),
                                    }
                                } else {
                                    panic!("unknown grammar production: {identifier}");
                                }
                            }
                            _ => panic!("the term {term} cannot appear in a grammar"),
                        }
                    }
                }
            }
            SetLogic(logic) => assert_eq!(logic, "SLIA"),
            CheckSynth => (),
            _ => panic!("Unknown command: {cmd:?}"),
        }
    }

    assert!(
        has_seen_synth_fun,
        "the input file did not contain a synth-fun command"
    );

    let problem = Problem {
        name,
        start: start.unwrap(),
        rules,
        args: fun_args,
        literals,
        examples,
    };

    println!("{}", serde_json::to_string_pretty(&problem).unwrap());
}
