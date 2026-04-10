/// Prelude: defines built-in types like Nat, Bool, Eq, and their eliminators.

use crate::core::Term;
use crate::env::{GlobalEnv, InductiveDef, ConstructorDef, Definition};

pub fn load_prelude(env: &mut GlobalEnv) {
    define_nat(env);
    define_bool(env);
    define_eq(env);
    define_and(env);
    define_or(env);
    define_empty(env);
    define_unit(env);
    define_basic_functions(env);
}

/// Natural numbers: inductive Nat : Type where | zero : Nat | succ : Nat → Nat
fn define_nat(env: &mut GlobalEnv) {
    let nat_ty = Term::Sort(1); // Type 0

    let zero_ty = Term::Global("Nat".to_string());
    let succ_ty = Term::Pi(
        "n".to_string(),
        Box::new(Term::Global("Nat".to_string())),
        Box::new(Term::Global("Nat".to_string())),
    );

    env.add_inductive(InductiveDef {
        name: "Nat".to_string(),
        params: vec![],
        ty: nat_ty,
        constructors: vec![
            ConstructorDef { name: "zero".to_string(), ty: zero_ty },
            ConstructorDef { name: "succ".to_string(), ty: succ_ty },
        ],
    });

    // Nat itself is a type
    env.defs.insert("Nat".to_string(), Definition::Axiom {
        ty: Term::Sort(1),
    });

    // Nat.rec : (motive : Nat → Sort u) → motive zero → ((n : Nat) → motive n → motive (succ n)) → (n : Nat) → motive n
    // Simplified: we rely on match expressions instead
}

/// Bool: inductive Bool : Type where | false : Bool | true : Bool
fn define_bool(env: &mut GlobalEnv) {
    let bool_ty = Term::Sort(1);

    env.add_inductive(InductiveDef {
        name: "Bool".to_string(),
        params: vec![],
        ty: bool_ty,
        constructors: vec![
            ConstructorDef {
                name: "Bool.false".to_string(),
                ty: Term::Global("Bool".to_string()),
            },
            ConstructorDef {
                name: "Bool.true".to_string(),
                ty: Term::Global("Bool".to_string()),
            },
        ],
    });

    env.defs.insert("Bool".to_string(), Definition::Axiom {
        ty: Term::Sort(1),
    });
}

/// Eq : {A : Type} → A → A → Prop
/// | refl : {A : Type} → {a : A} → Eq a a
fn define_eq(env: &mut GlobalEnv) {
    // Eq : {A : Type} → A → A → Prop
    let eq_ty = Term::Pi(
        "A".to_string(),
        Box::new(Term::Sort(1)),
        Box::new(Term::Pi(
            "_".to_string(),
            Box::new(Term::Var(0)),
            Box::new(Term::Pi(
                "_".to_string(),
                Box::new(Term::Var(1)),
                Box::new(Term::Sort(0)), // Prop
            )),
        )),
    );

    // Eq.refl : {A : Type} → {a : A} → Eq A a a
    let refl_ty = Term::Pi(
        "A".to_string(),
        Box::new(Term::Sort(1)),
        Box::new(Term::Pi(
            "a".to_string(),
            Box::new(Term::Var(0)),
            Box::new(Term::App(
                Box::new(Term::App(
                    Box::new(Term::App(
                        Box::new(Term::Global("Eq".to_string())),
                        Box::new(Term::Var(1)), // A
                    )),
                    Box::new(Term::Var(0)), // a
                )),
                Box::new(Term::Var(0)), // a
            )),
        )),
    );

    env.add_inductive(InductiveDef {
        name: "Eq".to_string(),
        params: vec![
            ("A".to_string(), Term::Sort(1)),
        ],
        ty: eq_ty.clone(),
        constructors: vec![
            ConstructorDef { name: "Eq.refl".to_string(), ty: refl_ty },
        ],
    });

    env.defs.insert("Eq".to_string(), Definition::Axiom { ty: eq_ty });
}

/// And : Prop → Prop → Prop (conjunction)
fn define_and(env: &mut GlobalEnv) {
    let and_ty = Term::Pi(
        "_".to_string(),
        Box::new(Term::Sort(0)),
        Box::new(Term::Pi(
            "_".to_string(),
            Box::new(Term::Sort(0)),
            Box::new(Term::Sort(0)),
        )),
    );

    let intro_ty = Term::Pi(
        "A".to_string(),
        Box::new(Term::Sort(0)),
        Box::new(Term::Pi(
            "B".to_string(),
            Box::new(Term::Sort(0)),
            Box::new(Term::Pi(
                "_".to_string(),
                Box::new(Term::Var(1)), // A
                Box::new(Term::Pi(
                    "_".to_string(),
                    Box::new(Term::Var(1)), // B
                    Box::new(Term::App(
                        Box::new(Term::App(
                            Box::new(Term::Global("And".to_string())),
                            Box::new(Term::Var(3)), // A
                        )),
                        Box::new(Term::Var(2)), // B
                    )),
                )),
            )),
        )),
    );

    env.add_inductive(InductiveDef {
        name: "And".to_string(),
        params: vec![],
        ty: and_ty.clone(),
        constructors: vec![
            ConstructorDef { name: "And.intro".to_string(), ty: intro_ty },
        ],
    });

    env.defs.insert("And".to_string(), Definition::Axiom { ty: and_ty });
}

/// Or : Prop → Prop → Prop (disjunction)
fn define_or(env: &mut GlobalEnv) {
    let or_ty = Term::Pi(
        "_".to_string(),
        Box::new(Term::Sort(0)),
        Box::new(Term::Pi(
            "_".to_string(),
            Box::new(Term::Sort(0)),
            Box::new(Term::Sort(0)),
        )),
    );

    let inl_ty = Term::Pi(
        "A".to_string(),
        Box::new(Term::Sort(0)),
        Box::new(Term::Pi(
            "B".to_string(),
            Box::new(Term::Sort(0)),
            Box::new(Term::Pi(
                "_".to_string(),
                Box::new(Term::Var(1)), // A
                Box::new(Term::App(
                    Box::new(Term::App(
                        Box::new(Term::Global("Or".to_string())),
                        Box::new(Term::Var(2)), // A
                    )),
                    Box::new(Term::Var(1)), // B
                )),
            )),
        )),
    );

    let inr_ty = Term::Pi(
        "A".to_string(),
        Box::new(Term::Sort(0)),
        Box::new(Term::Pi(
            "B".to_string(),
            Box::new(Term::Sort(0)),
            Box::new(Term::Pi(
                "_".to_string(),
                Box::new(Term::Var(0)), // B
                Box::new(Term::App(
                    Box::new(Term::App(
                        Box::new(Term::Global("Or".to_string())),
                        Box::new(Term::Var(2)), // A
                    )),
                    Box::new(Term::Var(1)), // B
                )),
            )),
        )),
    );

    env.add_inductive(InductiveDef {
        name: "Or".to_string(),
        params: vec![],
        ty: or_ty.clone(),
        constructors: vec![
            ConstructorDef { name: "Or.inl".to_string(), ty: inl_ty },
            ConstructorDef { name: "Or.inr".to_string(), ty: inr_ty },
        ],
    });

    env.defs.insert("Or".to_string(), Definition::Axiom { ty: or_ty });
}

/// Empty : Prop (falsehood, no constructors)
fn define_empty(env: &mut GlobalEnv) {
    env.add_inductive(InductiveDef {
        name: "Empty".to_string(),
        params: vec![],
        ty: Term::Sort(0),
        constructors: vec![],
    });

    env.defs.insert("Empty".to_string(), Definition::Axiom {
        ty: Term::Sort(0),
    });
}

/// Unit : Prop (truth, one constructor)
fn define_unit(env: &mut GlobalEnv) {
    env.add_inductive(InductiveDef {
        name: "Unit".to_string(),
        params: vec![],
        ty: Term::Sort(0),
        constructors: vec![
            ConstructorDef {
                name: "Unit.intro".to_string(),
                ty: Term::Global("Unit".to_string()),
            },
        ],
    });

    env.defs.insert("Unit".to_string(), Definition::Axiom {
        ty: Term::Sort(0),
    });
}

/// Define basic functions: add, mul, etc.
fn define_basic_functions(env: &mut GlobalEnv) {
    // Nat.add : Nat → Nat → Nat
    // Defined as: fun (n m : Nat) => match n with | zero => m | succ n' => succ (Nat.add n' m)
    let add_ty = Term::Pi(
        "n".to_string(),
        Box::new(Term::Global("Nat".to_string())),
        Box::new(Term::Pi(
            "m".to_string(),
            Box::new(Term::Global("Nat".to_string())),
            Box::new(Term::Global("Nat".to_string())),
        )),
    );

    let add_body = Term::Lam(
        "n".to_string(),
        Box::new(Term::Global("Nat".to_string())),
        Box::new(Term::Lam(
            "m".to_string(),
            Box::new(Term::Global("Nat".to_string())),
            Box::new(Term::Match {
                scrutinee: Box::new(Term::Var(1)), // n
                motive: None,
                arms: vec![
                    crate::core::MatchArm {
                        ctor: "zero".to_string(),
                        arity: 0,
                        body: Term::Var(0), // m (index 0 after entering match)
                    },
                    crate::core::MatchArm {
                        ctor: "succ".to_string(),
                        arity: 1,
                        body: Term::App(
                            Box::new(Term::Global("succ".to_string())),
                            Box::new(Term::App(
                                Box::new(Term::App(
                                    Box::new(Term::Global("Nat.add".to_string())),
                                    Box::new(Term::Var(0)), // n'
                                )),
                                Box::new(Term::Var(1)), // m
                            )),
                        ),
                    },
                ],
            }),
        )),
    );

    env.add_def("Nat.add".to_string(), add_ty.clone(), add_body);
    // Also register as `add`
    if let Some(def) = env.defs.get("Nat.add").cloned() {
        env.defs.insert("add".to_string(), def);
    }

    // Nat.mul : Nat → Nat → Nat
    let mul_ty = Term::Pi(
        "n".to_string(),
        Box::new(Term::Global("Nat".to_string())),
        Box::new(Term::Pi(
            "m".to_string(),
            Box::new(Term::Global("Nat".to_string())),
            Box::new(Term::Global("Nat".to_string())),
        )),
    );

    let mul_body = Term::Lam(
        "n".to_string(),
        Box::new(Term::Global("Nat".to_string())),
        Box::new(Term::Lam(
            "m".to_string(),
            Box::new(Term::Global("Nat".to_string())),
            Box::new(Term::Match {
                scrutinee: Box::new(Term::Var(1)),
                motive: None,
                arms: vec![
                    crate::core::MatchArm {
                        ctor: "zero".to_string(),
                        arity: 0,
                        body: Term::Nat(0),
                    },
                    crate::core::MatchArm {
                        ctor: "succ".to_string(),
                        arity: 1,
                        body: Term::App(
                            Box::new(Term::App(
                                Box::new(Term::Global("Nat.add".to_string())),
                                Box::new(Term::Var(1)), // m
                            )),
                            Box::new(Term::App(
                                Box::new(Term::App(
                                    Box::new(Term::Global("Nat.mul".to_string())),
                                    Box::new(Term::Var(0)), // n'
                                )),
                                Box::new(Term::Var(1)), // m
                            )),
                        ),
                    },
                ],
            }),
        )),
    );

    env.add_def("Nat.mul".to_string(), mul_ty, mul_body);
    if let Some(def) = env.defs.get("Nat.mul").cloned() {
        env.defs.insert("mul".to_string(), def);
    }

    // Not : Prop → Prop  (defined as A → Empty)
    let not_ty = Term::Pi(
        "_".to_string(),
        Box::new(Term::Sort(0)),
        Box::new(Term::Sort(0)),
    );
    let not_body = Term::Lam(
        "A".to_string(),
        Box::new(Term::Sort(0)),
        Box::new(Term::Pi(
            "_".to_string(),
            Box::new(Term::Var(0)),
            Box::new(Term::Global("Empty".to_string())),
        )),
    );
    env.add_def("Not".to_string(), not_ty, not_body);

    // sorry : {A : Sort u} → A (unsafe axiom for incomplete proofs)
    let sorry_ty = Term::Pi(
        "A".to_string(),
        Box::new(Term::Sort(1)),
        Box::new(Term::Var(0)),
    );
    env.add_axiom("sorry".to_string(), sorry_ty);

    // id : {A : Type} → A → A
    let id_ty = Term::Pi(
        "A".to_string(),
        Box::new(Term::Sort(1)),
        Box::new(Term::Pi(
            "a".to_string(),
            Box::new(Term::Var(0)),
            Box::new(Term::Var(1)),
        )),
    );
    let id_body = Term::Lam(
        "A".to_string(),
        Box::new(Term::Sort(1)),
        Box::new(Term::Lam(
            "a".to_string(),
            Box::new(Term::Var(0)),
            Box::new(Term::Var(0)),
        )),
    );
    env.add_def("id".to_string(), id_ty, id_body);
}
