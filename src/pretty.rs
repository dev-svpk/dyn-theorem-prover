/// Pretty printer for core terms — renders with human-readable variable names.

use crate::core::Term;

pub fn pretty_term(term: &Term) -> String {
    let mut ctx = Vec::new();
    pp(term, &mut ctx)
}

fn pp(term: &Term, ctx: &mut Vec<String>) -> String {
    match term {
        Term::Var(i) => {
            if *i < ctx.len() {
                ctx[ctx.len() - 1 - *i].clone()
            } else {
                format!("#{}", i)
            }
        }
        Term::Global(n) => n.clone(),
        Term::Sort(0) => "Prop".to_string(),
        Term::Sort(n) => {
            if *n == 1 {
                "Type".to_string()
            } else {
                format!("Type {}", n - 1)
            }
        }
        Term::Pi(name, a, b) => {
            if name == "_" {
                let a_str = pp_app(a, ctx);
                ctx.push("_".to_string());
                let b_str = pp(b, ctx);
                ctx.pop();
                format!("{} -> {}", a_str, b_str)
            } else {
                let a_str = pp(a, ctx);
                ctx.push(name.clone());
                let b_str = pp(b, ctx);
                ctx.pop();
                format!("({} : {}) -> {}", name, a_str, b_str)
            }
        }
        Term::Lam(name, a, body) => {
            let a_str = pp(a, ctx);
            ctx.push(name.clone());
            let body_str = pp(body, ctx);
            ctx.pop();
            format!("fun ({} : {}) => {}", name, a_str, body_str)
        }
        Term::App(f, x) => {
            let f_str = pp_func(f, ctx);
            let x_str = pp_atom(x, ctx);
            format!("{} {}", f_str, x_str)
        }
        Term::Let(name, ty, val, body) => {
            let ty_str = pp(ty, ctx);
            let val_str = pp(val, ctx);
            ctx.push(name.clone());
            let body_str = pp(body, ctx);
            ctx.pop();
            format!("let {} : {} := {} in {}", name, ty_str, val_str, body_str)
        }
        Term::Nat(n) => format!("{}", n),
        Term::BoolLit(b) => format!("{}", b),
        Term::Constructor(_ind, ctor) => ctor.clone(),
        Term::Recursor(ind) => format!("{}.rec", ind),
        Term::Match { scrutinee, arms, .. } => {
            let scrut_str = pp(scrutinee, ctx);
            let mut s = format!("match {} with", scrut_str);
            for arm in arms {
                // Push bindings for arm arity
                let arg_names: Vec<String> = (0..arm.arity)
                    .map(|i| format!("x{}", i))
                    .collect();
                for name in &arg_names {
                    ctx.push(name.clone());
                }
                let body_str = pp(&arm.body, ctx);
                for _ in 0..arm.arity {
                    ctx.pop();
                }
                if arm.arity > 0 {
                    s.push_str(&format!(" | {} {} => {}",
                        arm.ctor, arg_names.join(" "), body_str));
                } else {
                    s.push_str(&format!(" | {} => {}", arm.ctor, body_str));
                }
            }
            s.push_str(" end");
            s
        }
        Term::If(c, t, e) => {
            format!("if {} then {} else {}", pp(c, ctx), pp(t, ctx), pp(e, ctx))
        }
        Term::Meta(id) => format!("?{}", id),
        Term::Ann(e, ty) => format!("({} : {})", pp(e, ctx), pp(ty, ctx)),
    }
}

/// Print a term that appears in function position (no parens for App)
fn pp_func(term: &Term, ctx: &mut Vec<String>) -> String {
    match term {
        Term::Lam(..) | Term::Pi(..) | Term::Let(..) => format!("({})", pp(term, ctx)),
        _ => pp(term, ctx),
    }
}

/// Print a term at application level (parens for lam/pi/let/if, but not for app)
fn pp_app(term: &Term, ctx: &mut Vec<String>) -> String {
    match term {
        Term::Lam(..) | Term::Pi(..) | Term::Let(..) | Term::If(..) => format!("({})", pp(term, ctx)),
        _ => pp(term, ctx),
    }
}

/// Print a term that appears in argument position (parens for App, Lam, Pi)
fn pp_atom(term: &Term, ctx: &mut Vec<String>) -> String {
    match term {
        Term::App(..) | Term::Lam(..) | Term::Pi(..) | Term::Let(..) | Term::If(..)
            => format!("({})", pp(term, ctx)),
        _ => pp(term, ctx),
    }
}

/// Pretty print a value via quotation
use crate::core::Value;
use crate::env::GlobalEnv;
use crate::eval::quote;

pub fn pretty_value(val: &Value, lvl: usize, globals: &GlobalEnv) -> String {
    let term = quote(val, lvl, globals);
    pretty_term(&term)
}
