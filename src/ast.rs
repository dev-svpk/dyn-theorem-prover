/// Surface-level AST produced by the parser.
/// This is desugared into core `Term`s before type checking.

pub type Name = String;

/// Top-level commands in the language
#[derive(Debug, Clone)]
pub enum Command {
    /// `def name : type := body`
    Def {
        name: Name,
        ty: Option<Expr>,
        body: Expr,
    },
    /// `theorem name : type := body` or `theorem name : type by tactic`
    Theorem {
        name: Name,
        ty: Expr,
        body: ProofBody,
    },
    /// `axiom name : type`
    Axiom {
        name: Name,
        ty: Expr,
    },
    /// `inductive Name : type where | ctor1 : ty1 | ctor2 : ty2`
    Inductive {
        name: Name,
        params: Vec<(Name, Expr)>,
        ty: Expr,
        constructors: Vec<Constructor>,
    },
    /// `#check expr`
    Check(Expr),
    /// `#eval expr`
    Eval(Expr),
    /// `#print name`
    Print(Name),
    /// `example : type := body`
    Example {
        ty: Expr,
        body: ProofBody,
    },
}

#[derive(Debug, Clone)]
pub enum ProofBody {
    /// Direct term proof
    Term(Expr),
    /// Tactic proof: `by { tactic1; tactic2; ... }`
    Tactic(Vec<Tactic>),
}

#[derive(Debug, Clone)]
pub struct Constructor {
    pub name: Name,
    pub ty: Expr,
}

/// Surface-level expressions
#[derive(Debug, Clone)]
pub enum Expr {
    /// Variable reference
    Var(Name),
    /// Universe: `Type`, `Type 0`, `Type 1`, `Prop`
    Universe(u32),
    /// Prop (= Sort 0)
    Prop,
    /// Function application: `f x`
    App(Box<Expr>, Box<Expr>),
    /// Lambda: `fun (x : T) => body` or `λ (x : T) => body`
    Lam(Name, Box<Expr>, Box<Expr>),
    /// Pi / forall: `(x : A) -> B` or `forall (x : A), B`
    Pi(Name, Box<Expr>, Box<Expr>),
    /// Non-dependent arrow: `A -> B`
    Arrow(Box<Expr>, Box<Expr>),
    /// Let binding: `let x : T := e in body`
    Let(Name, Option<Box<Expr>>, Box<Expr>, Box<Expr>),
    /// Natural number literal
    Nat(u64),
    /// Boolean literal
    BoolLit(bool),
    /// If-then-else
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    /// Match expression: `match e with | pat1 => e1 | pat2 => e2`
    Match(Box<Expr>, Vec<MatchArm>),
    /// Hole / underscore: `_`
    Hole,
    /// Parenthesized expression (removed during desugar)
    Paren(Box<Expr>),
    /// Annotated expression: `(e : T)`
    Ann(Box<Expr>, Box<Expr>),
}

#[derive(Debug, Clone)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub body: Expr,
}

#[derive(Debug, Clone)]
pub enum Pattern {
    /// Constructor pattern: `Ctor x y z`
    Constructor(Name, Vec<Name>),
    /// Wildcard: `_`
    Wildcard,
    /// Variable binding
    Var(Name),
    /// Nat literal
    Nat(u64),
    /// Bool literal
    Bool(bool),
}

/// Tactics for proof mode
#[derive(Debug, Clone)]
pub enum Tactic {
    /// `intro x` or `intro x y z`
    Intro(Vec<Name>),
    /// `apply e`
    Apply(Expr),
    /// `exact e`
    Exact(Expr),
    /// `refl`
    Refl,
    /// `rw [e]` or `rewrite [e]`
    Rewrite(Expr),
    /// `cases e`
    Cases(Expr),
    /// `induction e`
    Induction(Expr),
    /// `simp`
    Simp,
    /// `assumption`
    Assumption,
    /// `constructor`
    ConstructorTac,
    /// `left`
    Left,
    /// `right`
    Right,
    /// `trivial`
    Trivial,
    /// `sorry` - admit a goal without proof
    Sorry,
    /// `have h : T := e` or `have h : T by { ... }`
    Have(Name, Expr, Box<ProofBody>),
    /// `show T`
    Show(Expr),
    /// `ring` - solve ring equations
    Ring,
}
