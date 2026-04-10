/// Global environment: stores definitions, axioms, inductive types, etc.

use std::collections::HashMap;
use crate::core::{Term, Name};

/// An inductive type definition
#[derive(Debug, Clone)]
pub struct InductiveDef {
    pub name: Name,
    /// Type parameters: (name, type)
    pub params: Vec<(Name, Term)>,
    /// The type of the inductive (e.g., Type 0)
    pub ty: Term,
    /// Constructors: (name, full type)
    pub constructors: Vec<ConstructorDef>,
}

#[derive(Debug, Clone)]
pub struct ConstructorDef {
    pub name: Name,
    pub ty: Term,
}

/// A definition in the environment
#[derive(Debug, Clone)]
pub enum Definition {
    /// A definition with a type and body
    Def {
        ty: Term,
        body: Term,
    },
    /// An axiom (no body, just a type)
    Axiom {
        ty: Term,
    },
    /// A constructor of an inductive type
    Constructor {
        inductive: Name,
        ty: Term,
        index: usize,
    },
    /// A recursor for an inductive type
    Recursor {
        inductive: Name,
        ty: Term,
    },
}

impl Definition {
    pub fn get_type(&self) -> &Term {
        match self {
            Definition::Def { ty, .. } => ty,
            Definition::Axiom { ty } => ty,
            Definition::Constructor { ty, .. } => ty,
            Definition::Recursor { ty, .. } => ty,
        }
    }
}

/// The global environment
#[derive(Debug, Clone)]
pub struct GlobalEnv {
    pub defs: HashMap<Name, Definition>,
    pub inductives: HashMap<Name, InductiveDef>,
}

impl GlobalEnv {
    pub fn new() -> Self {
        GlobalEnv {
            defs: HashMap::new(),
            inductives: HashMap::new(),
        }
    }

    pub fn add_def(&mut self, name: Name, ty: Term, body: Term) {
        self.defs.insert(name, Definition::Def { ty, body });
    }

    pub fn add_axiom(&mut self, name: Name, ty: Term) {
        self.defs.insert(name, Definition::Axiom { ty });
    }

    pub fn add_inductive(&mut self, ind: InductiveDef) {
        let ind_name = ind.name.clone();
        for (i, ctor) in ind.constructors.iter().enumerate() {
            self.defs.insert(
                ctor.name.clone(),
                Definition::Constructor {
                    inductive: ind_name.clone(),
                    ty: ctor.ty.clone(),
                    index: i,
                },
            );
        }
        self.inductives.insert(ind_name, ind);
    }

    pub fn lookup(&self, name: &str) -> Option<&Definition> {
        self.defs.get(name)
    }

    pub fn lookup_inductive(&self, name: &str) -> Option<&InductiveDef> {
        self.inductives.get(name)
    }
}
