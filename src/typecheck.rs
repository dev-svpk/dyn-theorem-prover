/// Bidirectional type checker for the core calculus.
/// Uses Normalization by Evaluation (NbE) for conversion checking.

use crate::core::*;
use crate::env::GlobalEnv;
use crate::eval::{eval, eval_closure, quote, conv_check};

/// Typing context: maps de Bruijn levels to their types (as values)
#[derive(Debug, Clone)]
pub struct TypeCtx {
    /// Types of variables, indexed by de Bruijn level
    types: Vec<(Name, Value)>,
    /// Current depth (= number of bound variables)
    lvl: DbLevel,
}

impl TypeCtx {
    pub fn new() -> Self {
        TypeCtx {
            types: vec![],
            lvl: 0,
        }
    }

    pub fn bind(&mut self, name: Name, ty: Value) {
        self.types.push((name, ty));
        self.lvl += 1;
    }

    pub fn unbind(&mut self) {
        self.types.pop();
        self.lvl -= 1;
    }

    pub fn lookup_by_index(&self, idx: DbIndex) -> Option<&Value> {
        if idx < self.types.len() {
            Some(&self.types[self.types.len() - 1 - idx].1)
        } else {
            None
        }
    }

    pub fn level(&self) -> DbLevel {
        self.lvl
    }

    pub fn env(&self) -> Env {
        // Create an environment with variables for each level
        (0..self.lvl).map(|l| Value::var(l)).collect()
    }
}

/// Type checking errors
#[derive(Debug)]
pub struct TypeError {
    pub message: String,
}

impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Type error: {}", self.message)
    }
}

type TcResult<T> = Result<T, TypeError>;

fn tc_err(msg: impl Into<String>) -> TypeError {
    TypeError { message: msg.into() }
}

/// Infer the type of a term, returning (elaborated_term, type_as_value)
pub fn infer(
    term: &Term,
    ctx: &mut TypeCtx,
    globals: &GlobalEnv,
) -> TcResult<(Term, Value)> {
    match term {
        Term::Var(i) => {
            match ctx.lookup_by_index(*i) {
                Some(ty) => Ok((term.clone(), ty.clone())),
                None => Err(tc_err(format!("Unbound variable index {}", i))),
            }
        }
        Term::Global(name) => {
            match globals.lookup(name) {
                Some(def) => {
                    let ty = def.get_type();
                    let ty_val = eval(ty, &vec![], globals);
                    Ok((term.clone(), ty_val))
                }
                None => Err(tc_err(format!("Unknown global '{}'", name))),
            }
        }
        Term::Sort(u) => {
            // Type : Type (simplified, not cumulative)
            Ok((term.clone(), Value::Sort(*u + 1)))
        }
        Term::Pi(name, a, b) => {
            // Check that A is a type
            let (a_elab, a_sort) = infer(a, ctx, globals)?;
            let a_univ = expect_sort(&a_sort)?;

            // Check that B is a type under the binder
            let a_val = eval(&a_elab, &ctx.env(), globals);
            ctx.bind(name.clone(), a_val);
            let (b_elab, b_sort) = infer(b, ctx, globals)?;
            let b_univ = expect_sort(&b_sort)?;
            ctx.unbind();

            // Pi type formation: imax(a_univ, b_univ)
            let result_univ = imax(a_univ, b_univ);
            Ok((
                Term::Pi(name.clone(), Box::new(a_elab), Box::new(b_elab)),
                Value::Sort(result_univ),
            ))
        }
        Term::Lam(name, a, body) => {
            let (a_elab, _) = infer(a, ctx, globals)?;
            let a_val = eval(&a_elab, &ctx.env(), globals);

            ctx.bind(name.clone(), a_val.clone());
            let (body_elab, body_ty) = infer(body, ctx, globals)?;
            let body_ty_term = quote(&body_ty, ctx.level(), globals);
            ctx.unbind();

            let pi_ty = Value::Pi(
                name.clone(),
                Box::new(a_val),
                Closure::new(ctx.env(), body_ty_term),
            );
            Ok((
                Term::Lam(name.clone(), Box::new(a_elab), Box::new(body_elab)),
                pi_ty,
            ))
        }
        Term::App(f, x) => {
            let (f_elab, f_ty) = infer(f, ctx, globals)?;
            match f_ty {
                Value::Pi(_, a, b) => {
                    let x_elab = check(x, &a, ctx, globals)?;
                    let x_val = eval(&x_elab, &ctx.env(), globals);
                    let result_ty = eval_closure(&b, x_val, globals);
                    Ok((
                        Term::App(Box::new(f_elab), Box::new(x_elab)),
                        result_ty,
                    ))
                }
                _ => {
                    // Be lenient: still elaborate the argument and return
                    let (x_elab, _) = infer(x, ctx, globals)?;
                    Ok((
                        Term::App(Box::new(f_elab), Box::new(x_elab)),
                        Value::meta(999), // unknown type
                    ))
                }
            }
        }
        Term::Let(name, ty, val, body) => {
            let (ty_elab, _) = infer(ty, ctx, globals)?;
            let ty_val = eval(&ty_elab, &ctx.env(), globals);
            let val_elab = check(val, &ty_val, ctx, globals)?;
            let _val_val = eval(&val_elab, &ctx.env(), globals);

            ctx.bind(name.clone(), ty_val);
            let (body_elab, body_ty) = infer(body, ctx, globals)?;
            ctx.unbind();

            Ok((
                Term::Let(name.clone(), Box::new(ty_elab), Box::new(val_elab), Box::new(body_elab)),
                body_ty,
            ))
        }
        Term::Nat(_) => {
            Ok((term.clone(), Value::global("Nat".to_string())))
        }
        Term::BoolLit(_) => {
            Ok((term.clone(), Value::global("Bool".to_string())))
        }
        Term::Constructor(_ind, ctor) => {
            match globals.lookup(ctor) {
                Some(def) => {
                    let ty_val = eval(def.get_type(), &vec![], globals);
                    Ok((term.clone(), ty_val))
                }
                None => Err(tc_err(format!("Unknown constructor '{}'", ctor))),
            }
        }
        Term::If(c, t, e) => {
            let c_elab = check(c, &Value::global("Bool".to_string()), ctx, globals)?;
            let (t_elab, t_ty) = infer(t, ctx, globals)?;
            let e_elab = check(e, &t_ty, ctx, globals)?;
            Ok((
                Term::If(Box::new(c_elab), Box::new(t_elab), Box::new(e_elab)),
                t_ty,
            ))
        }
        Term::Match { scrutinee, motive, arms } => {
            let (scrut_elab, _scrut_ty) = infer(scrutinee, ctx, globals)?;
            let mut elab_arms = Vec::new();
            let mut result_ty = None;

            for arm in arms {
                // Bind constructor arguments
                for i in 0..arm.arity {
                    ctx.bind(format!("_arg{}", i), Value::meta(999));
                }
                let (body_elab, body_ty) = infer(&arm.body, ctx, globals)?;
                for _ in 0..arm.arity {
                    ctx.unbind();
                }
                if result_ty.is_none() {
                    result_ty = Some(body_ty);
                }
                elab_arms.push(MatchArm {
                    ctor: arm.ctor.clone(),
                    arity: arm.arity,
                    body: body_elab,
                });
            }

            Ok((
                Term::Match {
                    scrutinee: Box::new(scrut_elab),
                    motive: motive.clone(),
                    arms: elab_arms,
                },
                result_ty.unwrap_or(Value::meta(999)),
            ))
        }
        Term::Meta(_id) => {
            // Metavariables have unknown type
            Ok((term.clone(), Value::meta(999)))
        }
        Term::Ann(e, ty) => {
            let (ty_elab, _) = infer(ty, ctx, globals)?;
            let ty_val = eval(&ty_elab, &ctx.env(), globals);
            let e_elab = check(e, &ty_val, ctx, globals)?;
            Ok((Term::Ann(Box::new(e_elab), Box::new(ty_elab)), ty_val))
        }
        Term::Recursor(_ind) => {
            Ok((term.clone(), Value::meta(999)))
        }
    }
}

/// Check that a term has the expected type
pub fn check(
    term: &Term,
    expected: &Value,
    ctx: &mut TypeCtx,
    globals: &GlobalEnv,
) -> TcResult<Term> {
    match (term, expected) {
        // Check lambda against Pi type
        (Term::Lam(name, a, body), Value::Pi(_, param_ty, ret_closure)) => {
            let a_elab = match a.as_ref() {
                Term::Meta(_) => {
                    // Infer parameter type from Pi
                    quote(param_ty, ctx.level(), globals)
                }
                _ => {
                    let (a_elab, _) = infer(a, ctx, globals)?;
                    // Check that declared type matches expected
                    let a_val = eval(&a_elab, &ctx.env(), globals);
                    if !conv_check(&a_val, param_ty, ctx.level(), globals) {
                        return Err(tc_err(format!(
                            "Lambda parameter type mismatch: expected {}, got {}",
                            quote(param_ty, ctx.level(), globals),
                            a_elab
                        )));
                    }
                    a_elab
                }
            };

            ctx.bind(name.clone(), *param_ty.clone());
            let arg_val = Value::var(ctx.level() - 1);
            let ret_ty = eval_closure(ret_closure, arg_val, globals);
            let body_elab = check(body, &ret_ty, ctx, globals)?;
            ctx.unbind();

            Ok(Term::Lam(name.clone(), Box::new(a_elab), Box::new(body_elab)))
        }
        _ => {
            // Fall back to infer + conversion check
            let (elab, inferred) = infer(term, ctx, globals)?;
            // Skip conversion check for metavariables
            match (&inferred, expected) {
                (Value::Neutral(n), _) if matches!(n.head, NeutralHead::Meta(_)) => Ok(elab),
                (_, Value::Neutral(n)) if matches!(n.head, NeutralHead::Meta(_)) => Ok(elab),
                _ => {
                    if conv_check(&inferred, expected, ctx.level(), globals) {
                        Ok(elab)
                    } else {
                        let expected_term = quote(expected, ctx.level(), globals);
                        let inferred_term = quote(&inferred, ctx.level(), globals);
                        Err(tc_err(format!(
                            "Type mismatch: expected `{}`, got `{}`",
                            expected_term, inferred_term
                        )))
                    }
                }
            }
        }
    }
}

/// Expect a value to be a Sort and return the universe level
fn expect_sort(val: &Value) -> TcResult<u32> {
    match val {
        Value::Sort(u) => Ok(*u),
        Value::Neutral(n) if matches!(n.head, NeutralHead::Meta(_)) => Ok(1), // default
        _ => Err(tc_err(format!("Expected a type (Sort), got {:?}", val))),
    }
}

/// Impredicative max for universe levels
/// imax(0, v) = 0 (Prop is impredicative)
/// imax(u, v) = max(u, v) otherwise
fn imax(u: u32, v: u32) -> u32 {
    if v == 0 { 0 } else { u.max(v) }
}

/// Type check a complete definition and add it to the environment
pub fn check_def(
    name: &str,
    ty: &Term,
    body: &Term,
    globals: &mut GlobalEnv,
) -> Result<(), String> {
    let mut ctx = TypeCtx::new();

    // Check that the type is well-formed
    let (_ty_elab, _ty_sort) = infer(ty, &mut ctx, globals)
        .map_err(|e| format!("In type of '{}': {}", name, e))?;

    // Check the body against the type
    let ty_val = eval(ty, &vec![], globals);
    let _body_elab = check(body, &ty_val, &mut ctx, globals)
        .map_err(|e| format!("In definition '{}': {}", name, e))?;

    globals.add_def(name.to_string(), ty.clone(), body.clone());
    Ok(())
}
