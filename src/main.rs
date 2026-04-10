#![allow(unused)]

mod ast;
mod ast_helpers;
mod core;
mod env;
mod elaborate;
mod eval;
mod typecheck;
mod tactics;
mod pretty;
mod prelude;
mod driver;

use lalrpop_util::lalrpop_mod;

lalrpop_mod!(pub grammar, "/grammar.rs");

use std::env as std_env;
use std::fs;

fn main() {
    let args: Vec<String> = std_env::args().collect();

    let mut globals = env::GlobalEnv::new();
    prelude::load_prelude(&mut globals);

    if args.len() > 1 {
        // File mode: process a source file
        let filename = &args[1];
        match fs::read_to_string(filename) {
            Ok(source) => {
                process_source(&source, &mut globals);
            }
            Err(e) => {
                eprintln!("Error reading file '{}': {}", filename, e);
                std::process::exit(1);
            }
        }
    } else {
        // REPL mode
        run_repl(&mut globals);
    }
}

fn process_source(source: &str, globals: &mut env::GlobalEnv) {
    let parser = grammar::ProgramParser::new();
    match parser.parse(source) {
        Ok(commands) => {
            for cmd in &commands {
                match driver::process_command(cmd, globals) {
                    Ok(msg) => println!("{}", msg),
                    Err(e) => eprintln!("Error: {}", e),
                }
            }
        }
        Err(e) => {
            eprintln!("Parse error: {}", e);
        }
    }
}

fn run_repl(globals: &mut env::GlobalEnv) {
    println!("╔══════════════════════════════════════════════╗");
    println!("║  DynTP — Dynamic Theorem Prover v0.1.0      ║");
    println!("║  A Lean-like language for interactive proofs ║");
    println!("║  Type :help for usage, :quit to exit         ║");
    println!("╚══════════════════════════════════════════════╝");
    println!();

    let mut rl = match rustyline::DefaultEditor::new() {
        Ok(rl) => rl,
        Err(e) => {
            eprintln!("Failed to initialize readline: {}", e);
            // Fallback to basic stdin reading
            run_basic_repl(globals);
            return;
        }
    };

    let parser = grammar::ProgramParser::new();
    let mut buffer = String::new();

    loop {
        let prompt = if buffer.is_empty() { "dyntp> " } else { "  ...> " };
        match rl.readline(prompt) {
            Ok(line) => {
                let trimmed = line.trim();

                // Handle REPL commands
                if buffer.is_empty() {
                    match trimmed {
                        ":quit" | ":q" | ":exit" => {
                            println!("Goodbye!");
                            break;
                        }
                        ":help" | ":h" => {
                            print_help();
                            continue;
                        }
                        ":env" => {
                            print_env(globals);
                            continue;
                        }
                        _ => {}
                    }
                }

                buffer.push_str(&line);
                buffer.push('\n');

                // Try to parse the accumulated buffer
                match parser.parse(&buffer) {
                    Ok(commands) => {
                        let _ = rl.add_history_entry(buffer.trim());
                        for cmd in &commands {
                            match driver::process_command(cmd, globals) {
                                Ok(msg) => println!("{}", msg),
                                Err(e) => eprintln!("Error: {}", e),
                            }
                        }
                        buffer.clear();
                    }
                    Err(lalrpop_util::ParseError::UnrecognizedEof { .. }) => {
                        // Incomplete input, continue reading
                        continue;
                    }
                    Err(e) => {
                        eprintln!("Parse error: {}", e);
                        buffer.clear();
                    }
                }
            }
            Err(rustyline::error::ReadlineError::Interrupted) => {
                buffer.clear();
                println!("(interrupted)");
            }
            Err(rustyline::error::ReadlineError::Eof) => {
                println!("Goodbye!");
                break;
            }
            Err(e) => {
                eprintln!("Error: {}", e);
                break;
            }
        }
    }
}

fn run_basic_repl(globals: &mut env::GlobalEnv) {
    use std::io::{self, BufRead, Write};

    let stdin = io::stdin();
    let parser = grammar::ProgramParser::new();
    let mut buffer = String::new();

    loop {
        if buffer.is_empty() {
            print!("dyntp> ");
        } else {
            print!("  ...> ");
        }
        io::stdout().flush().unwrap();

        let mut line = String::new();
        match stdin.lock().read_line(&mut line) {
            Ok(0) => break, // EOF
            Ok(_) => {
                let trimmed = line.trim();
                if buffer.is_empty() {
                    match trimmed {
                        ":quit" | ":q" | ":exit" => break,
                        ":help" | ":h" => {
                            print_help();
                            continue;
                        }
                        ":env" => {
                            print_env(globals);
                            continue;
                        }
                        _ => {}
                    }
                }

                buffer.push_str(&line);

                match parser.parse(&buffer) {
                    Ok(commands) => {
                        for cmd in &commands {
                            match driver::process_command(cmd, globals) {
                                Ok(msg) => println!("{}", msg),
                                Err(e) => eprintln!("Error: {}", e),
                            }
                        }
                        buffer.clear();
                    }
                    Err(lalrpop_util::ParseError::UnrecognizedEof { .. }) => continue,
                    Err(e) => {
                        eprintln!("Parse error: {}", e);
                        buffer.clear();
                    }
                }
            }
            Err(e) => {
                eprintln!("Error: {}", e);
                break;
            }
        }
    }
}

fn print_help() {
    println!("Commands:");
    println!("  def <name> : <type> := <body>       Define a value");
    println!("  theorem <name> : <type> := <proof>   Prove a theorem");
    println!("  theorem <name> : <type> := by {{ }}    Prove with tactics");
    println!("  axiom <name> : <type>                Declare an axiom");
    println!("  inductive <name> : <type> where ...  Define inductive type");
    println!("  #check <expr>                        Check the type of an expression");
    println!("  #eval <expr>                         Evaluate an expression");
    println!("  #print <name>                        Print a definition");
    println!();
    println!("Types:");
    println!("  Prop, Type, Type 0, Type 1, ...      Universes");
    println!("  Nat, Bool, Eq, And, Or, Empty, Unit  Built-in types");
    println!("  (x : A) -> B  or  forall (x : A), B Pi/forall types");
    println!("  A -> B                                Non-dependent function type");
    println!();
    println!("Expressions:");
    println!("  fun (x : T) => body                  Lambda abstraction");
    println!("  f x                                  Application");
    println!("  let x : T := e in body               Let binding");
    println!("  match e with | p1 => e1 | p2 => e2   Pattern matching");
    println!("  if c then t else e                   Conditional");
    println!();
    println!("Tactics:");
    println!("  intro x y z    Introduce hypotheses");
    println!("  exact e        Provide exact proof term");
    println!("  apply e        Apply a function/theorem");
    println!("  refl           Prove reflexivity (a = a)");
    println!("  assumption     Use a hypothesis");
    println!("  cases e        Case split");
    println!("  induction e    Structural induction");
    println!("  simp           Simplification");
    println!("  sorry          Admit (incomplete proof)");
    println!();
    println!("REPL:");
    println!("  :help          Show this help");
    println!("  :env           Show the environment");
    println!("  :quit          Exit");
}

fn print_env(globals: &env::GlobalEnv) {
    use crate::pretty::pretty_term;
    println!("── Definitions ──");
    let mut names: Vec<&String> = globals.defs.keys().collect();
    names.sort();
    for name in names {
        if let Some(def) = globals.defs.get(name) {
            match def {
                env::Definition::Def { ty, .. } => {
                    println!("  def {} : {}", name, pretty_term(ty));
                }
                env::Definition::Axiom { ty } => {
                    println!("  axiom {} : {}", name, pretty_term(ty));
                }
                env::Definition::Constructor { inductive, ty, .. } => {
                    println!("  ctor {}.{} : {}", inductive, name, pretty_term(ty));
                }
                env::Definition::Recursor { inductive, ty } => {
                    println!("  rec {}.rec : {}", inductive, pretty_term(ty));
                }
            }
        }
    }
    println!("── Inductive Types ──");
    let mut ind_names: Vec<&String> = globals.inductives.keys().collect();
    ind_names.sort();
    for name in ind_names {
        if let Some(ind) = globals.inductives.get(name) {
            println!("  inductive {} : {}", name, pretty_term(&ind.ty));
            for ctor in &ind.constructors {
                println!("    | {} : {}", ctor.name, pretty_term(&ctor.ty));
            }
        }
    }
}
