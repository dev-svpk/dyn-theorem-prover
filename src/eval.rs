/// Normalization by Evaluation (NbE) for the core calculus.
/// This evaluates terms to values and reads back values to terms.

use crate::core::*;
use crate::env::{GlobalEnv, Definition};

/// Evaluate a term to a value in the given environment
pub fn eval(term: &Term, env: &Env, globals: &GlobalEnv) -> Value {
    match term {
        Term::Var(i) => {
            if *i < env.len() {
                env[env.len() - 1 - *i].clone()
            } else {
                Value::var(0) // shouldn't happen in well-typed terms
            }
        }
        Term::Global(name) => {
            match globals.lookup(name) {
                Some(Definition::Def { body, .. }) => eval(body, &vec![], globals),
                Some(Definition::Constructor { inductive, .. }) => {
                    Value::Constructor(inductive.clone(), name.clone(), vec![])
                }
                _ => Value::global(name.clone()),
            }
        }
        Term::Sort(u) => Value::Sort(*u),
        Term::Pi(name, a, b) => {
            let a_val = eval(a, env, globals);
            Value::Pi(name.clone(), Box::new(a_val), Closure::new(env.clone(), *b.clone()))
        }
        Term::Lam(name, a, body) => {
            let a_val = eval(a, env, globals);
            Value::Lam(name.clone(), Box::new(a_val), Closure::new(env.clone(), *body.clone()))
        }
        Term::App(f, x) => {
            let f_val = eval(f, env, globals);
            let x_val = eval(x, env, globals);
            do_app(f_val, x_val, globals)
        }
        Term::Let(_name, _ty, val, body) => {
            let val_v = eval(val, env, globals);
            let mut new_env = env.clone();
            new_env.push(val_v);
            eval(body, &new_env, globals)
        }
        Term::Nat(n) => Value::Nat(*n),
        Term::BoolLit(b) => Value::BoolLit(*b),
        Term::Constructor(ind, ctor) => {
            Value::Constructor(ind.clone(), ctor.clone(), vec![])
        }
        Term::Recursor(_ind) => {
            // Recursors are handled via Match
            Value::global(format!("{}.rec", _ind))
        }
        Term::Match { scrutinee, motive, arms } => {
            let scrut_val = eval(scrutinee, env, globals);
            let motive_val = motive.as_ref().map(|m| eval(m, env, globals));
            let arm_closures: Vec<(Name, usize, Closure)> = arms.iter().map(|arm| {
                (arm.ctor.clone(), arm.arity, Closure::new(env.clone(), arm.body.clone()))
            }).collect();
            do_match(scrut_val, motive_val, arm_closures, globals)
        }
        Term::If(c, t, e) => {
            let c_val = eval(c, env, globals);
            let t_val = eval(t, env, globals);
            let e_val = eval(e, env, globals);
            do_if(c_val, t_val, e_val, globals)
        }
        Term::Meta(id) => Value::meta(*id),
        Term::Ann(e, _ty) => eval(e, env, globals),
    }
}

/// Apply a function value to an argument
pub fn do_app(f: Value, arg: Value, globals: &GlobalEnv) -> Value {
    match f {
        Value::Lam(_, _, closure) => eval_closure(&closure, arg, globals),
        Value::Neutral(mut n) => {
            n.spine.push(Elim::App(arg));
            Value::Neutral(n)
        }
        Value::Constructor(ind, ctor, mut args) => {
            args.push(arg.clone());
            // Special handling for Nat: succ n => Nat(n+1)
            if (ctor == "succ" || ctor == "Nat.succ") && args.len() == 1 {
                if let Value::Nat(n) = &args[0] {
                    return Value::Nat(n + 1);
                }
            }
            Value::Constructor(ind, ctor, args)
        }
        _ => {
            // Error: trying to apply a non-function
            Value::Neutral(Neutral {
                head: NeutralHead::Global("error:app-non-function".to_string()),
                spine: vec![Elim::App(f), Elim::App(arg)],
            })
        }
    }
}

/// Evaluate a closure with a given argument
pub fn eval_closure(closure: &Closure, arg: Value, globals: &GlobalEnv) -> Value {
    let mut env = closure.env.clone();
    env.push(arg);
    eval(&closure.body, &env, globals)
}

/// Perform a match elimination
fn do_match(
    scrutinee: Value,
    motive: Option<Value>,
    arms: Vec<(Name, usize, Closure)>,
    globals: &GlobalEnv,
) -> Value {
    match &scrutinee {
        Value::Constructor(_ind, ctor, ctor_args) => {
            // Find matching arm
            for (arm_ctor, _arity, closure) in &arms {
                if arm_ctor == ctor {
                    // Apply the closure to all constructor arguments
                    let mut env = closure.env.clone();
                    for arg in ctor_args {
                        env.push(arg.clone());
                    }
                    return eval(&closure.body, &env, globals);
                }
            }
            // No matching arm — this is an error in a well-typed program
            scrutinee
        }
        Value::Nat(n) => {
            // Match on natural numbers: 0 matches "zero", n+1 matches "succ"
            if *n == 0 {
                for (arm_ctor, _, closure) in &arms {
                    if arm_ctor == "zero" || arm_ctor == "Nat.zero" {
                        return eval(&closure.body, &closure.env, globals);
                    }
                }
            } else {
                for (arm_ctor, _, closure) in &arms {
                    if arm_ctor == "succ" || arm_ctor == "Nat.succ" {
                        let mut env = closure.env.clone();
                        env.push(Value::Nat(n - 1));
                        return eval(&closure.body, &env, globals);
                    }
                }
            }
            scrutinee
        }
        Value::BoolLit(b) => {
            let target = if *b { "true" } else { "false" };
            for (arm_ctor, _, closure) in &arms {
                if arm_ctor == target || arm_ctor == &format!("Bool.{}", target) {
                    return eval(&closure.body, &closure.env, globals);
                }
            }
            scrutinee
        }
        Value::Neutral(n) => {
            let mut n = n.clone();
            n.spine.push(Elim::Match {
                motive,
                arms: arms,
            });
            Value::Neutral(n)
        }
        _ => scrutinee,
    }
}

/// Perform if-then-else elimination
fn do_if(cond: Value, then_val: Value, else_val: Value, _globals: &GlobalEnv) -> Value {
    match cond {
        Value::BoolLit(true) => then_val,
        Value::BoolLit(false) => else_val,
        Value::Neutral(mut n) => {
            n.spine.push(Elim::If(then_val, else_val));
            Value::Neutral(n)
        }
        _ => then_val, // fallback
    }
}

/// Read back a value to a term (quotation) at a given level
pub fn quote(val: &Value, lvl: DbLevel, globals: &GlobalEnv) -> Term {
    match val {
        Value::Sort(u) => Term::Sort(*u),
        Value::Lam(name, ty, closure) => {
            let ty_term = quote(ty, lvl, globals);
            let arg = Value::var(lvl);
            let body_val = eval_closure(closure, arg, globals);
            let body_term = quote(&body_val, lvl + 1, globals);
            Term::Lam(name.clone(), Box::new(ty_term), Box::new(body_term))
        }
        Value::Pi(name, a, closure) => {
            let a_term = quote(a, lvl, globals);
            let arg = Value::var(lvl);
            let b_val = eval_closure(closure, arg, globals);
            let b_term = quote(&b_val, lvl + 1, globals);
            Term::Pi(name.clone(), Box::new(a_term), Box::new(b_term))
        }
        Value::Nat(n) => Term::Nat(*n),
        Value::BoolLit(b) => Term::BoolLit(*b),
        Value::Constructor(ind, ctor, args) => {
            let mut term = Term::Constructor(ind.clone(), ctor.clone());
            for arg in args {
                term = Term::App(Box::new(term), Box::new(quote(arg, lvl, globals)));
            }
            term
        }
        Value::Neutral(n) => quote_neutral(n, lvl, globals),
    }
}

fn quote_neutral(n: &Neutral, lvl: DbLevel, globals: &GlobalEnv) -> Term {
    let head = match &n.head {
        NeutralHead::Var(l) => Term::Var(lvl - 1 - l),
        NeutralHead::Global(name) => Term::Global(name.clone()),
        NeutralHead::Meta(id) => Term::Meta(*id),
    };

    n.spine.iter().fold(head, |acc, elim| {
        match elim {
            Elim::App(v) => Term::App(Box::new(acc), Box::new(quote(v, lvl, globals))),
            Elim::Match { arms, .. } => {
                let arms_terms: Vec<crate::core::MatchArm> = arms.iter().map(|(ctor, arity, closure)| {
                    // Create variables for the arm bindings
                    let mut env = closure.env.clone();
                    for i in 0..*arity {
                        env.push(Value::var(lvl + i));
                    }
                    let body_val = eval(&closure.body, &env, globals);
                    let body_term = quote(&body_val, lvl + *arity, globals);
                    crate::core::MatchArm {
                        ctor: ctor.clone(),
                        arity: *arity,
                        body: body_term,
                    }
                }).collect();
                Term::Match {
                    scrutinee: Box::new(acc),
                    motive: None,
                    arms: arms_terms,
                }
            }
            Elim::If(t, e) => {
                Term::If(
                    Box::new(acc),
                    Box::new(quote(t, lvl, globals)),
                    Box::new(quote(e, lvl, globals)),
                )
            }
        }
    })
}

/// Normalize a term fully
pub fn normalize(term: &Term, env: &Env, globals: &GlobalEnv) -> Term {
    let val = eval(term, env, globals);
    let lvl = env.len();
    quote(&val, lvl, globals)
}

/// Check if two values are definitionally equal
pub fn conv_check(v1: &Value, v2: &Value, lvl: DbLevel, globals: &GlobalEnv) -> bool {
    match (v1, v2) {
        (Value::Sort(u1), Value::Sort(u2)) => u1 == u2,
        (Value::Nat(n1), Value::Nat(n2)) => n1 == n2,
        (Value::BoolLit(b1), Value::BoolLit(b2)) => b1 == b2,
        (Value::Pi(_, a1, b1), Value::Pi(_, a2, b2)) => {
            if !conv_check(a1, a2, lvl, globals) {
                return false;
            }
            let arg = Value::var(lvl);
            let b1_val = eval_closure(b1, arg.clone(), globals);
            let b2_val = eval_closure(b2, arg, globals);
            conv_check(&b1_val, &b2_val, lvl + 1, globals)
        }
        (Value::Lam(_, _, b1), Value::Lam(_, _, b2)) => {
            let arg = Value::var(lvl);
            let b1_val = eval_closure(b1, arg.clone(), globals);
            let b2_val = eval_closure(b2, arg, globals);
            conv_check(&b1_val, &b2_val, lvl + 1, globals)
        }
        // Eta-expand: f == λx. f x
        (Value::Lam(_, _, closure), other) | (other, Value::Lam(_, _, closure)) => {
            let arg = Value::var(lvl);
            let body = eval_closure(closure, arg.clone(), globals);
            let other_app = do_app(other.clone(), arg, globals);
            conv_check(&body, &other_app, lvl + 1, globals)
        }
        (Value::Constructor(i1, c1, a1), Value::Constructor(i2, c2, a2)) => {
            i1 == i2 && c1 == c2 && a1.len() == a2.len()
                && a1.iter().zip(a2.iter()).all(|(x, y)| conv_check(x, y, lvl, globals))
        }
        (Value::Neutral(n1), Value::Neutral(n2)) => {
            conv_neutral(n1, n2, lvl, globals)
        }
        _ => false,
    }
}

fn conv_neutral(n1: &Neutral, n2: &Neutral, lvl: DbLevel, globals: &GlobalEnv) -> bool {
    let heads_eq = match (&n1.head, &n2.head) {
        (NeutralHead::Var(l1), NeutralHead::Var(l2)) => l1 == l2,
        (NeutralHead::Global(n1), NeutralHead::Global(n2)) => n1 == n2,
        (NeutralHead::Meta(id1), NeutralHead::Meta(id2)) => id1 == id2,
        _ => false,
    };
    if !heads_eq || n1.spine.len() != n2.spine.len() {
        return false;
    }
    n1.spine.iter().zip(n2.spine.iter()).all(|(e1, e2)| {
        match (e1, e2) {
            (Elim::App(v1), Elim::App(v2)) => conv_check(v1, v2, lvl, globals),
            _ => false, // Simplification: only compare App elims
        }
    })
}
