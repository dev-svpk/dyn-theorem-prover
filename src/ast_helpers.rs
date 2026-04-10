use crate::ast::*;

pub fn wrap_lams(params: Vec<(Name, Expr)>, body: Expr) -> Expr {
    params.into_iter().rev().fold(body, |acc, (name, ty)| {
        Expr::Lam(name, Box::new(ty), Box::new(acc))
    })
}

pub fn wrap_pis(params: Vec<(Name, Expr)>, body: Expr) -> Expr {
    params.into_iter().rev().fold(body, |acc, (name, ty)| {
        Expr::Pi(name, Box::new(ty), Box::new(acc))
    })
}
