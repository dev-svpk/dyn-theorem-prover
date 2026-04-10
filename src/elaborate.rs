/// Elaboration: translates surface AST (Expr) into core Term,
/// performing name resolution, type inference, and hole filling.

use crate::ast;
use crate::core::{Term, Name};
use crate::env::GlobalEnv;

/// Local context for name resolution
#[derive(Debug, Clone)]
pub struct LocalCtx {
    /// Stack of bound variable names (most recent last)
    names: Vec<Name>,
}

impl LocalCtx {
    pub fn new() -> Self {
        LocalCtx { names: vec![] }
    }

    pub fn bind(&mut self, name: Name) {
        self.names.push(name);
    }

    pub fn unbind(&mut self) {
        self.names.pop();
    }

    pub fn lookup(&self, name: &str) -> Option<usize> {
        // Return de Bruijn index (0 = most recently bound)
        for (i, n) in self.names.iter().rev().enumerate() {
            if n == name {
                return Some(i);
            }
        }
        None
    }

    pub fn depth(&self) -> usize {
        self.names.len()
    }
}

/// Elaborate a surface expression to a core term
pub fn elaborate_expr(expr: &ast::Expr, ctx: &mut LocalCtx, globals: &GlobalEnv) -> Result<Term, String> {
    match expr {
        ast::Expr::Var(name) => {
            // First check local context
            if let Some(idx) = ctx.lookup(name) {
                return Ok(Term::Var(idx));
            }
            // Then check globals
            if globals.lookup(name).is_some() {
                return Ok(Term::Global(name.clone()));
            }
            // Check if it's a constructor
            if globals.defs.contains_key(name) {
                return Ok(Term::Global(name.clone()));
            }
            // Might be a forward reference or unknown — treat as global
            Ok(Term::Global(name.clone()))
        }
        ast::Expr::Universe(n) => Ok(Term::Sort(*n + 1)),
        ast::Expr::Prop => Ok(Term::Sort(0)),
        ast::Expr::App(f, x) => {
            let f_term = elaborate_expr(f, ctx, globals)?;
            let x_term = elaborate_expr(x, ctx, globals)?;
            Ok(Term::App(Box::new(f_term), Box::new(x_term)))
        }
        ast::Expr::Lam(name, ty, body) => {
            let ty_term = elaborate_expr(ty, ctx, globals)?;
            ctx.bind(name.clone());
            let body_term = elaborate_expr(body, ctx, globals)?;
            ctx.unbind();
            Ok(Term::Lam(name.clone(), Box::new(ty_term), Box::new(body_term)))
        }
        ast::Expr::Pi(name, ty, body) => {
            let ty_term = elaborate_expr(ty, ctx, globals)?;
            ctx.bind(name.clone());
            let body_term = elaborate_expr(body, ctx, globals)?;
            ctx.unbind();
            Ok(Term::Pi(name.clone(), Box::new(ty_term), Box::new(body_term)))
        }
        ast::Expr::Arrow(a, b) => {
            let a_term = elaborate_expr(a, ctx, globals)?;
            ctx.bind("_".to_string());
            let b_term = elaborate_expr(b, ctx, globals)?;
            ctx.unbind();
            Ok(Term::Pi("_".to_string(), Box::new(a_term), Box::new(b_term)))
        }
        ast::Expr::Let(name, ty, val, body) => {
            let ty_term = match ty {
                Some(t) => elaborate_expr(t, ctx, globals)?,
                None => Term::Meta(0), // placeholder
            };
            let val_term = elaborate_expr(val, ctx, globals)?;
            ctx.bind(name.clone());
            let body_term = elaborate_expr(body, ctx, globals)?;
            ctx.unbind();
            Ok(Term::Let(
                name.clone(),
                Box::new(ty_term),
                Box::new(val_term),
                Box::new(body_term),
            ))
        }
        ast::Expr::Nat(n) => Ok(Term::Nat(*n)),
        ast::Expr::BoolLit(b) => Ok(Term::BoolLit(*b)),
        ast::Expr::If(c, t, e) => {
            let c_term = elaborate_expr(c, ctx, globals)?;
            let t_term = elaborate_expr(t, ctx, globals)?;
            let e_term = elaborate_expr(e, ctx, globals)?;
            Ok(Term::If(Box::new(c_term), Box::new(t_term), Box::new(e_term)))
        }
        ast::Expr::Match(scrutinee, arms) => {
            let scrut_term = elaborate_expr(scrutinee, ctx, globals)?;
            let mut core_arms = Vec::new();
            for arm in arms {
                let (ctor_name, bound_names) = match &arm.pattern {
                    ast::Pattern::Constructor(name, args) => (name.clone(), args.clone()),
                    ast::Pattern::Var(name) => (name.clone(), vec![]),
                    ast::Pattern::Wildcard => ("_".to_string(), vec![]),
                    ast::Pattern::Nat(0) => ("zero".to_string(), vec![]),
                    ast::Pattern::Nat(_n) => {
                        return Err("Only 0 literal patterns supported in match; use Nat.succ n instead".to_string());
                    }
                    ast::Pattern::Bool(true) => ("true".to_string(), vec![]),
                    ast::Pattern::Bool(false) => ("false".to_string(), vec![]),
                };

                let arity = bound_names.len();
                for name in &bound_names {
                    ctx.bind(name.clone());
                }
                let body_term = elaborate_expr(&arm.body, ctx, globals)?;
                for _ in &bound_names {
                    ctx.unbind();
                }

                core_arms.push(crate::core::MatchArm {
                    ctor: ctor_name,
                    arity,
                    body: body_term,
                });
            }
            Ok(Term::Match {
                scrutinee: Box::new(scrut_term),
                motive: None,
                arms: core_arms,
            })
        }
        ast::Expr::Hole => {
            // Generate a metavariable
            Ok(Term::Meta(0))
        }
        ast::Expr::Paren(e) => elaborate_expr(e, ctx, globals),
        ast::Expr::Ann(e, ty) => {
            let e_term = elaborate_expr(e, ctx, globals)?;
            let ty_term = elaborate_expr(ty, ctx, globals)?;
            Ok(Term::Ann(Box::new(e_term), Box::new(ty_term)))
        }
    }
}

/// Elaborate a constructor definition type
pub fn elaborate_constructor_type(
    expr: &ast::Expr,
    _ind_name: &str,
    _params: &[(ast::Name, ast::Expr)],
    ctx: &mut LocalCtx,
    globals: &GlobalEnv,
) -> Result<Term, String> {
    elaborate_expr(expr, ctx, globals)
}
