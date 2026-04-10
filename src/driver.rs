/// Driver: processes top-level commands, coordinates parsing,
/// elaboration, type checking, and evaluation.

use crate::ast::{Command, ProofBody};
use crate::core::Term;
use crate::env::{GlobalEnv, InductiveDef, ConstructorDef, Definition};
use crate::elaborate::{self, LocalCtx};
use crate::eval::{eval, quote};
use crate::typecheck::{self, TypeCtx};
use crate::tactics::{self, Goal};
use crate::pretty::pretty_term;

/// Process a single command
pub fn process_command(cmd: &Command, globals: &mut GlobalEnv) -> Result<String, String> {
    match cmd {
        Command::Def { name, ty, body } => process_def(name, ty.as_ref(), body, globals),
        Command::Theorem { name, ty, body } => process_theorem(name, ty, body, globals),
        Command::Axiom { name, ty } => process_axiom(name, ty, globals),
        Command::Inductive { name, params, ty, constructors } => {
            process_inductive(name, params, ty, constructors, globals)
        }
        Command::Check(expr) => process_check(expr, globals),
        Command::Eval(expr) => process_eval(expr, globals),
        Command::Print(name) => process_print(name, globals),
        Command::Example { ty, body } => process_example(ty, body, globals),
    }
}

fn process_def(
    name: &str,
    ty: Option<&crate::ast::Expr>,
    body: &crate::ast::Expr,
    globals: &mut GlobalEnv,
) -> Result<String, String> {
    let mut ctx = LocalCtx::new();

    // If a type annotation is given, pre-register it so recursive references work
    let ty_term = if let Some(ty_expr) = ty {
        let t = elaborate::elaborate_expr(ty_expr, &mut ctx, globals)?;
        // Pre-register as axiom so the body can reference the name recursively
        globals.add_axiom(name.to_string(), t.clone());
        Some(t)
    } else {
        None
    };

    let body_term = elaborate::elaborate_expr(body, &mut ctx, globals)?;

    let ty_term = if let Some(t) = ty_term {
        t
    } else {
        // Infer type
        let mut tc_ctx = TypeCtx::new();
        let (_, ty_val) = typecheck::infer(&body_term, &mut tc_ctx, globals)
            .map_err(|e| e.to_string())?;
        quote(&ty_val, 0, globals)
    };

    // Type check
    let mut tc_ctx = TypeCtx::new();
    let ty_val = eval(&ty_term, &vec![], globals);
    let _ = typecheck::check(&body_term, &ty_val, &mut tc_ctx, globals)
        .map_err(|e| e.to_string())?;

    // Replace the axiom with the full definition
    globals.add_def(name.to_string(), ty_term.clone(), body_term);
    Ok(format!("'{}' defined : {}", name, pretty_term(&ty_term)))
}

fn process_theorem(
    name: &str,
    ty_expr: &crate::ast::Expr,
    body: &ProofBody,
    globals: &mut GlobalEnv,
) -> Result<String, String> {
    let mut ctx = LocalCtx::new();
    let ty_term = elaborate::elaborate_expr(ty_expr, &mut ctx, globals)?;
    let ty_val = eval(&ty_term, &vec![], globals);

    let proof_term = match body {
        ProofBody::Term(expr) => {
            let term = elaborate::elaborate_expr(expr, &mut ctx, globals)?;
            // Type check
            let mut tc_ctx = TypeCtx::new();
            let _ = typecheck::check(&term, &ty_val, &mut tc_ctx, globals)
                .map_err(|e| e.to_string())?;
            term
        }
        ProofBody::Tactic(tactics) => {
            let goal = Goal::new(ty_val.clone(), ty_term.clone());
            tactics::run_tactics(tactics, goal, globals)?
        }
    };

    globals.add_def(name.to_string(), ty_term.clone(), proof_term);
    Ok(format!("theorem '{}' proved : {}", name, pretty_term(&ty_term)))
}

fn process_axiom(
    name: &str,
    ty_expr: &crate::ast::Expr,
    globals: &mut GlobalEnv,
) -> Result<String, String> {
    let mut ctx = LocalCtx::new();
    let ty_term = elaborate::elaborate_expr(ty_expr, &mut ctx, globals)?;

    // Check well-formedness of the type
    let mut tc_ctx = TypeCtx::new();
    let _ = typecheck::infer(&ty_term, &mut tc_ctx, globals)
        .map_err(|e| e.to_string())?;

    globals.add_axiom(name.to_string(), ty_term.clone());
    Ok(format!("axiom '{}' : {}", name, pretty_term(&ty_term)))
}

fn process_inductive(
    name: &str,
    params: &[(String, crate::ast::Expr)],
    ty_expr: &crate::ast::Expr,
    ctors: &[crate::ast::Constructor],
    globals: &mut GlobalEnv,
) -> Result<String, String> {
    let mut ctx = LocalCtx::new();

    // Elaborate parameters
    let mut elab_params = Vec::new();
    for (pname, pty) in params {
        let pty_term = elaborate::elaborate_expr(pty, &mut ctx, globals)?;
        ctx.bind(pname.clone());
        elab_params.push((pname.clone(), pty_term));
    }

    let ty_term = elaborate::elaborate_expr(ty_expr, &mut ctx, globals)?;

    // Elaborate constructors
    let mut elab_ctors = Vec::new();
    for ctor in ctors {
        let ctor_ty = elaborate::elaborate_expr(&ctor.ty, &mut ctx, globals)?;
        elab_ctors.push(ConstructorDef {
            name: ctor.name.clone(),
            ty: ctor_ty,
        });
    }

    // Unbind parameters
    for _ in params {
        ctx.unbind();
    }

    // Register the inductive type
    env_add_inductive(globals, name, &elab_params, &ty_term, &elab_ctors);

    let mut msg = format!("inductive '{}' defined", name);
    for ctor in &elab_ctors {
        msg.push_str(&format!("\n  | {} : {}", ctor.name, pretty_term(&ctor.ty)));
    }
    Ok(msg)
}

fn env_add_inductive(
    globals: &mut GlobalEnv,
    name: &str,
    params: &[(String, Term)],
    ty: &Term,
    ctors: &[ConstructorDef],
) {
    // Add the type itself
    globals.defs.insert(name.to_string(), Definition::Axiom {
        ty: ty.clone(),
    });

    globals.add_inductive(InductiveDef {
        name: name.to_string(),
        params: params.to_vec(),
        ty: ty.clone(),
        constructors: ctors.to_vec(),
    });
}

fn process_check(
    expr: &crate::ast::Expr,
    globals: &GlobalEnv,
) -> Result<String, String> {
    let mut ctx = LocalCtx::new();
    let term = elaborate::elaborate_expr(expr, &mut ctx, globals)?;

    let mut tc_ctx = TypeCtx::new();
    let (elab, ty_val) = typecheck::infer(&term, &mut tc_ctx, globals)
        .map_err(|e| e.to_string())?;

    let ty_term = quote(&ty_val, 0, globals);
    Ok(format!("{} : {}", pretty_term(&elab), pretty_term(&ty_term)))
}

fn process_eval(
    expr: &crate::ast::Expr,
    globals: &GlobalEnv,
) -> Result<String, String> {
    let mut ctx = LocalCtx::new();
    let term = elaborate::elaborate_expr(expr, &mut ctx, globals)?;

    let val = eval(&term, &vec![], globals);
    let result = quote(&val, 0, globals);
    Ok(format!("{}", pretty_term(&result)))
}

fn process_print(
    name: &str,
    globals: &GlobalEnv,
) -> Result<String, String> {
    match globals.lookup(name) {
        Some(Definition::Def { ty, body }) => {
            Ok(format!("def {} : {} :=\n  {}", name, pretty_term(ty), pretty_term(body)))
        }
        Some(Definition::Axiom { ty }) => {
            Ok(format!("axiom {} : {}", name, pretty_term(ty)))
        }
        Some(Definition::Constructor { inductive, ty, .. }) => {
            Ok(format!("constructor {}.{} : {}", inductive, name, pretty_term(ty)))
        }
        Some(Definition::Recursor { inductive, ty }) => {
            Ok(format!("recursor {}.rec : {}", inductive, pretty_term(ty)))
        }
        None => {
            // Check if it's an inductive type
            match globals.lookup_inductive(name) {
                Some(ind) => {
                    let mut msg = format!("inductive {} : {}", name, pretty_term(&ind.ty));
                    for ctor in &ind.constructors {
                        msg.push_str(&format!("\n  | {} : {}", ctor.name, pretty_term(&ctor.ty)));
                    }
                    Ok(msg)
                }
                None => Err(format!("Unknown name '{}'", name)),
            }
        }
    }
}

fn process_example(
    ty_expr: &crate::ast::Expr,
    body: &ProofBody,
    globals: &mut GlobalEnv,
) -> Result<String, String> {
    let mut ctx = LocalCtx::new();
    let ty_term = elaborate::elaborate_expr(ty_expr, &mut ctx, globals)?;
    let ty_val = eval(&ty_term, &vec![], globals);

    let _proof_term = match body {
        ProofBody::Term(expr) => {
            let term = elaborate::elaborate_expr(expr, &mut ctx, globals)?;
            let mut tc_ctx = TypeCtx::new();
            let _ = typecheck::check(&term, &ty_val, &mut tc_ctx, globals)
                .map_err(|e| e.to_string())?;
            term
        }
        ProofBody::Tactic(tactics) => {
            let goal = Goal::new(ty_val.clone(), ty_term.clone());
            tactics::run_tactics(tactics, goal, globals)?
        }
    };

    Ok(format!("example : {} ✓", pretty_term(&ty_term)))
}
