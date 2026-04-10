/// Core type theory terms — the internal representation after elaboration.
/// Based on the Calculus of Inductive Constructions.

use std::fmt;

pub type Name = String;

/// De Bruijn index for bound variables
pub type DbIndex = usize;

/// De Bruijn level for free variables (used during evaluation)
pub type DbLevel = usize;

/// Core terms of the type theory
#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    /// Bound variable (de Bruijn index)
    Var(DbIndex),
    /// Free/global variable (by name)
    Global(Name),
    /// Universe: Sort(0) = Prop, Sort(n+1) = Type n
    Sort(u32),
    /// Dependent function type: Π(x : A). B
    Pi(Name, Box<Term>, Box<Term>),
    /// Lambda abstraction: λ(x : A). body
    Lam(Name, Box<Term>, Box<Term>),
    /// Application: f a
    App(Box<Term>, Box<Term>),
    /// Let binding: let x : A = e in body
    Let(Name, Box<Term>, Box<Term>, Box<Term>),
    /// Natural number literal
    Nat(u64),
    /// Bool literal
    BoolLit(bool),
    /// Constructor reference: Inductive.Constructor
    Constructor(Name, Name),
    /// Recursor/eliminator: Inductive.rec
    Recursor(Name),
    /// Match/pattern match (compiled form)
    Match {
        scrutinee: Box<Term>,
        motive: Option<Box<Term>>,
        arms: Vec<MatchArm>,
    },
    /// If-then-else (sugar, desugars to Bool.rec)
    If(Box<Term>, Box<Term>, Box<Term>),
    /// Metavariable (for unification / holes)
    Meta(MetaId),
    /// Type annotation: (e : T)
    Ann(Box<Term>, Box<Term>),
}

pub type MetaId = usize;

#[derive(Debug, Clone, PartialEq)]
pub struct MatchArm {
    pub ctor: Name,
    pub arity: usize,
    pub body: Term,
}

/// Values — the result of evaluation (used for type checking via NbE)
#[derive(Debug, Clone)]
pub enum Value {
    /// Neutral term: a variable applied to arguments that can't reduce further
    Neutral(Neutral),
    /// Sort value
    Sort(u32),
    /// Lambda closure
    Lam(Name, Box<Value>, Closure),
    /// Pi type value
    Pi(Name, Box<Value>, Closure),
    /// Natural number
    Nat(u64),
    /// Bool
    BoolLit(bool),
    /// Constructor value (fully or partially applied)
    Constructor(Name, Name, Vec<Value>),
}

/// A neutral term is a variable (free) with a spine of eliminators
#[derive(Debug, Clone)]
pub struct Neutral {
    pub head: NeutralHead,
    pub spine: Vec<Elim>,
}

#[derive(Debug, Clone)]
pub enum NeutralHead {
    /// Free variable (level)
    Var(DbLevel),
    /// Global definition (not yet unfolded, or axiom)
    Global(Name),
    /// Metavariable
    Meta(MetaId),
}

#[derive(Debug, Clone)]
pub enum Elim {
    /// Function application
    App(Value),
    /// Match elimination
    Match {
        motive: Option<Value>,
        arms: Vec<(Name, usize, Closure)>,
    },
    /// If elimination
    If(Value, Value),
}

/// A closure captures an environment for evaluating under a binder
#[derive(Debug, Clone)]
pub struct Closure {
    pub env: Env,
    pub body: Term,
}

/// Environment mapping de Bruijn indices to values
pub type Env = Vec<Value>;

impl Closure {
    pub fn new(env: Env, body: Term) -> Self {
        Closure { env, body }
    }
}

impl Value {
    pub fn var(level: DbLevel) -> Value {
        Value::Neutral(Neutral {
            head: NeutralHead::Var(level),
            spine: vec![],
        })
    }

    pub fn global(name: Name) -> Value {
        Value::Neutral(Neutral {
            head: NeutralHead::Global(name),
            spine: vec![],
        })
    }

    pub fn meta(id: MetaId) -> Value {
        Value::Neutral(Neutral {
            head: NeutralHead::Meta(id),
            spine: vec![],
        })
    }
}

impl Term {
    /// Shift de Bruijn indices by `amount` for indices >= `cutoff`
    pub fn shift(&self, cutoff: usize, amount: isize) -> Term {
        match self {
            Term::Var(i) => {
                if *i >= cutoff {
                    Term::Var((*i as isize + amount) as usize)
                } else {
                    Term::Var(*i)
                }
            }
            Term::Global(n) => Term::Global(n.clone()),
            Term::Sort(u) => Term::Sort(*u),
            Term::Pi(n, a, b) => Term::Pi(
                n.clone(),
                Box::new(a.shift(cutoff, amount)),
                Box::new(b.shift(cutoff + 1, amount)),
            ),
            Term::Lam(n, a, body) => Term::Lam(
                n.clone(),
                Box::new(a.shift(cutoff, amount)),
                Box::new(body.shift(cutoff + 1, amount)),
            ),
            Term::App(f, x) => Term::App(
                Box::new(f.shift(cutoff, amount)),
                Box::new(x.shift(cutoff, amount)),
            ),
            Term::Let(n, ty, val, body) => Term::Let(
                n.clone(),
                Box::new(ty.shift(cutoff, amount)),
                Box::new(val.shift(cutoff, amount)),
                Box::new(body.shift(cutoff + 1, amount)),
            ),
            Term::Nat(n) => Term::Nat(*n),
            Term::BoolLit(b) => Term::BoolLit(*b),
            Term::Constructor(ind, ctor) => Term::Constructor(ind.clone(), ctor.clone()),
            Term::Recursor(ind) => Term::Recursor(ind.clone()),
            Term::Match { scrutinee, motive, arms } => Term::Match {
                scrutinee: Box::new(scrutinee.shift(cutoff, amount)),
                motive: motive.as_ref().map(|m| Box::new(m.shift(cutoff, amount))),
                arms: arms.iter().map(|arm| MatchArm {
                    ctor: arm.ctor.clone(),
                    arity: arm.arity,
                    body: arm.body.shift(cutoff + arm.arity, amount),
                }).collect(),
            },
            Term::If(c, t, e) => Term::If(
                Box::new(c.shift(cutoff, amount)),
                Box::new(t.shift(cutoff, amount)),
                Box::new(e.shift(cutoff, amount)),
            ),
            Term::Meta(id) => Term::Meta(*id),
            Term::Ann(e, ty) => Term::Ann(
                Box::new(e.shift(cutoff, amount)),
                Box::new(ty.shift(cutoff, amount)),
            ),
        }
    }

    /// Substitute `term` for variable at index `idx`
    pub fn subst(&self, idx: usize, term: &Term) -> Term {
        match self {
            Term::Var(i) => {
                if *i == idx {
                    term.clone()
                } else if *i > idx {
                    Term::Var(*i - 1)
                } else {
                    Term::Var(*i)
                }
            }
            Term::Global(n) => Term::Global(n.clone()),
            Term::Sort(u) => Term::Sort(*u),
            Term::Pi(n, a, b) => Term::Pi(
                n.clone(),
                Box::new(a.subst(idx, term)),
                Box::new(b.subst(idx + 1, &term.shift(0, 1))),
            ),
            Term::Lam(n, a, body) => Term::Lam(
                n.clone(),
                Box::new(a.subst(idx, term)),
                Box::new(body.subst(idx + 1, &term.shift(0, 1))),
            ),
            Term::App(f, x) => Term::App(
                Box::new(f.subst(idx, term)),
                Box::new(x.subst(idx, term)),
            ),
            Term::Let(n, ty, val, body) => Term::Let(
                n.clone(),
                Box::new(ty.subst(idx, term)),
                Box::new(val.subst(idx, term)),
                Box::new(body.subst(idx + 1, &term.shift(0, 1))),
            ),
            Term::Nat(n) => Term::Nat(*n),
            Term::BoolLit(b) => Term::BoolLit(*b),
            Term::Constructor(ind, ctor) => Term::Constructor(ind.clone(), ctor.clone()),
            Term::Recursor(ind) => Term::Recursor(ind.clone()),
            Term::Match { scrutinee, motive, arms } => Term::Match {
                scrutinee: Box::new(scrutinee.subst(idx, term)),
                motive: motive.as_ref().map(|m| Box::new(m.subst(idx, term))),
                arms: arms.iter().map(|arm| MatchArm {
                    ctor: arm.ctor.clone(),
                    arity: arm.arity,
                    body: arm.body.subst(idx + arm.arity, &term.shift(0, arm.arity as isize)),
                }).collect(),
            },
            Term::If(c, t, e) => Term::If(
                Box::new(c.subst(idx, term)),
                Box::new(t.subst(idx, term)),
                Box::new(e.subst(idx, term)),
            ),
            Term::Meta(id) => Term::Meta(*id),
            Term::Ann(e, ty) => Term::Ann(
                Box::new(e.subst(idx, term)),
                Box::new(ty.subst(idx, term)),
            ),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(i) => write!(f, "#{}", i),
            Term::Global(n) => write!(f, "{}", n),
            Term::Sort(0) => write!(f, "Prop"),
            Term::Sort(n) => write!(f, "Type {}", n - 1),
            Term::Pi(n, a, b) => {
                if n == "_" {
                    write!(f, "{} → {}", a, b)
                } else {
                    write!(f, "∀ ({} : {}), {}", n, a, b)
                }
            }
            Term::Lam(n, a, body) => write!(f, "fun ({} : {}) => {}", n, a, body),
            Term::App(func, arg) => {
                let func_str = match func.as_ref() {
                    Term::Lam(..) | Term::Pi(..) => format!("({})", func),
                    _ => format!("{}", func),
                };
                let arg_str = match arg.as_ref() {
                    Term::App(..) | Term::Lam(..) | Term::Pi(..) => format!("({})", arg),
                    _ => format!("{}", arg),
                };
                write!(f, "{} {}", func_str, arg_str)
            }
            Term::Let(n, ty, val, body) => {
                write!(f, "let {} : {} := {} in {}", n, ty, val, body)
            }
            Term::Nat(n) => write!(f, "{}", n),
            Term::BoolLit(b) => write!(f, "{}", b),
            Term::Constructor(_ind, ctor) => write!(f, "{}", ctor),
            Term::Recursor(ind) => write!(f, "{}.rec", ind),
            Term::Match { scrutinee, arms, .. } => {
                write!(f, "match {} with", scrutinee)?;
                for arm in arms {
                    write!(f, " | {} => {}", arm.ctor, arm.body)?;
                }
                Ok(())
            }
            Term::If(c, t, e) => write!(f, "if {} then {} else {}", c, t, e),
            Term::Meta(id) => write!(f, "?{}", id),
            Term::Ann(e, ty) => write!(f, "({} : {})", e, ty),
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Neutral(n) => write!(f, "{}", n),
            Value::Sort(0) => write!(f, "Prop"),
            Value::Sort(n) => write!(f, "Type {}", n - 1),
            Value::Lam(name, ty, _) => write!(f, "fun ({} : {}) => ...", name, ty),
            Value::Pi(name, a, _) => {
                if name == "_" {
                    write!(f, "{} → ...", a)
                } else {
                    write!(f, "∀ ({} : {}), ...", name, a)
                }
            }
            Value::Nat(n) => write!(f, "{}", n),
            Value::BoolLit(b) => write!(f, "{}", b),
            Value::Constructor(_ind, ctor, args) => {
                if args.is_empty() {
                    write!(f, "{}", ctor)
                } else {
                    write!(f, "({}", ctor)?;
                    for a in args {
                        write!(f, " {}", a)?;
                    }
                    write!(f, ")")
                }
            }
        }
    }
}

impl fmt::Display for Neutral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.head {
            NeutralHead::Var(lvl) => write!(f, "v{}", lvl)?,
            NeutralHead::Global(n) => write!(f, "{}", n)?,
            NeutralHead::Meta(id) => write!(f, "?{}", id)?,
        }
        for elim in &self.spine {
            match elim {
                Elim::App(v) => write!(f, " {}", v)?,
                Elim::Match { .. } => write!(f, " .match{{...}}")?,
                Elim::If(_, _) => write!(f, " .if{{...}}")?,
            }
        }
        Ok(())
    }
}
