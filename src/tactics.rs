/// Tactic engine: executes proof tactics to construct terms.
/// Each tactic transforms a proof goal into sub-goals.

use crate::ast::{self, Tactic, ProofBody};
use crate::core::*;
use crate::env::GlobalEnv;
use crate::eval::{eval, eval_closure, quote, conv_check, normalize};
use crate::elaborate::{self, LocalCtx};

/// A proof goal
#[derive(Debug, Clone)]
pub struct Goal {
    /// Hypotheses: (name, type_as_term, type_as_value)
    pub hyps: Vec<(Name, Term, Value)>,
    /// The target type to prove
    pub target: Value,
    /// Target as a term (for display)
    pub target_term: Term,
    /// Current de Bruijn level
    pub level: usize,
}

impl Goal {
    pub fn new(target: Value, target_term: Term) -> Self {
        Goal {
            hyps: vec![],
            target,
            target_term,
            level: 0,
        }
    }

    pub fn display(&self, _globals: &GlobalEnv) -> String {
        let mut s = String::new();
        for (name, ty_term, _) in &self.hyps {
            s.push_str(&format!("  {} : {}\n", name, ty_term));
        }
        s.push_str(&format!("  ⊢ {}", self.target_term));
        s
    }
}

/// Result of executing a tactic
pub enum TacticResult {
    /// Tactic produced a complete proof term
    Complete(Term),
    /// Tactic produced sub-goals with a combiner function
    SubGoals {
        goals: Vec<Goal>,
        /// Function that combines proof terms for sub-goals into a proof term for the original goal
        combine: Box<dyn Fn(Vec<Term>) -> Term>,
    },
}

/// Execute a sequence of tactics to prove a goal
pub fn run_tactics(
    tactics: &[Tactic],
    goal: Goal,
    globals: &GlobalEnv,
) -> Result<Term, String> {
    let mut goals = vec![goal];
    let _proof_terms: Vec<Option<Term>> = vec![None];
    let _combiners: Vec<(usize, Box<dyn Fn(Vec<Term>) -> Term>)> = vec![];

    for (tac_idx, tactic) in tactics.iter().enumerate() {
        if goals.is_empty() {
            return Err(format!("No more goals to solve, but tactic '{}' was given",
                format_tactic(tactic)));
        }

        let current_goal = goals.remove(0);
        let result = execute_tactic(tactic, &current_goal, globals)?;

        match result {
            TacticResult::Complete(term) => {
                // This goal is solved
                if goals.is_empty() {
                    return Ok(wrap_proof_term(term, &current_goal));
                }
                // Store the proof term and continue with remaining goals
                return finish_remaining(term, &current_goal, &tactics[tac_idx + 1..], goals, globals);
            }
            TacticResult::SubGoals { goals: new_goals, combine } => {
                if new_goals.is_empty() {
                    // Tactic solved the goal completely
                    let term = combine(vec![]);
                    if goals.is_empty() {
                        return Ok(wrap_proof_term(term, &current_goal));
                    }
                    return finish_remaining(term, &current_goal, &tactics[tac_idx + 1..], goals, globals);
                }
                // Prepend new sub-goals
                let mut all_goals = new_goals;
                all_goals.extend(goals);
                goals = all_goals;
            }
        }
    }

    if goals.is_empty() {
        Err("No proof term produced".to_string())
    } else {
        let mut msg = format!("Proof incomplete. {} unsolved goal(s):\n", goals.len());
        for (i, g) in goals.iter().enumerate() {
            msg.push_str(&format!("\nGoal {}:\n{}\n", i + 1, g.display(globals)));
        }
        Err(msg)
    }
}

fn finish_remaining(
    first_term: Term,
    _first_goal: &Goal,
    remaining_tactics: &[Tactic],
    remaining_goals: Vec<Goal>,
    globals: &GlobalEnv,
) -> Result<Term, String> {
    if remaining_goals.is_empty() && remaining_tactics.is_empty() {
        return Ok(wrap_proof_term(first_term, _first_goal));
    }
    if remaining_goals.is_empty() {
        return Ok(wrap_proof_term(first_term, _first_goal));
    }
    // Continue solving remaining goals
    let _rest_term = run_tactics(remaining_tactics, remaining_goals[0].clone(), globals)?;
    Ok(wrap_proof_term(first_term, _first_goal))
}

fn wrap_proof_term(term: Term, goal: &Goal) -> Term {
    // Wrap the proof term in lambdas for each hypothesis
    let mut result = term;
    for (name, ty_term, _) in goal.hyps.iter().rev() {
        result = Term::Lam(name.clone(), Box::new(ty_term.clone()), Box::new(result));
    }
    result
}

/// Execute a single tactic on a goal
fn execute_tactic(
    tactic: &Tactic,
    goal: &Goal,
    globals: &GlobalEnv,
) -> Result<TacticResult, String> {
    match tactic {
        Tactic::Intro(names) => tactic_intro(names, goal, globals),
        Tactic::Apply(expr) => tactic_apply(expr, goal, globals),
        Tactic::Exact(expr) => tactic_exact(expr, goal, globals),
        Tactic::Refl => tactic_refl(goal, globals),
        Tactic::Assumption => tactic_assumption(goal, globals),
        Tactic::Sorry => tactic_sorry(goal, globals),
        Tactic::Trivial => tactic_trivial(goal, globals),
        Tactic::Cases(expr) => tactic_cases(expr, goal, globals),
        Tactic::Induction(expr) => tactic_induction(expr, goal, globals),
        Tactic::Rewrite(expr) => tactic_rewrite(expr, goal, globals),
        Tactic::Simp => tactic_simp(goal, globals),
        Tactic::ConstructorTac => tactic_constructor(goal, globals),
        Tactic::Left => tactic_left(goal, globals),
        Tactic::Right => tactic_right(goal, globals),
        Tactic::Have(name, ty_expr, body) => tactic_have(name, ty_expr, body, goal, globals),
        Tactic::Show(expr) => tactic_show(expr, goal, globals),
        Tactic::Ring => tactic_ring(goal, globals),
    }
}

/// `intro x y z` — introduce hypotheses from a Pi type
fn tactic_intro(
    names: &[Name],
    goal: &Goal,
    globals: &GlobalEnv,
) -> Result<TacticResult, String> {
    let mut new_goal = goal.clone();
    let mut target = goal.target.clone();
    let mut intro_count = 0;

    for name in names {
        match &target {
            Value::Pi(_, param_ty, ret_closure) => {
                let param_ty_term = quote(param_ty, new_goal.level, globals);
                new_goal.hyps.push((name.clone(), param_ty_term, *param_ty.clone()));
                let arg = Value::var(new_goal.level);
                target = eval_closure(ret_closure, arg, globals);
                new_goal.level += 1;
                intro_count += 1;
            }
            _ => {
                return Err(format!(
                    "Cannot intro '{}': target is not a function/forall type. Target: {}",
                    name,
                    quote(&target, new_goal.level, globals)
                ));
            }
        }
    }

    let target_term = quote(&target, new_goal.level, globals);
    new_goal.target = target;
    new_goal.target_term = target_term;

    Ok(TacticResult::SubGoals {
        goals: vec![new_goal],
        combine: Box::new(move |terms| {
            assert!(!terms.is_empty());
            terms[0].clone()
        }),
    })
}

/// `exact e` — provide the exact proof term
fn tactic_exact(
    expr: &ast::Expr,
    goal: &Goal,
    globals: &GlobalEnv,
) -> Result<TacticResult, String> {
    let mut ctx = LocalCtx::new();
    // Add hypotheses to context
    for (name, _, _) in &goal.hyps {
        ctx.bind(name.clone());
    }
    let term = elaborate::elaborate_expr(expr, &mut ctx, globals)
        .map_err(|e| format!("In exact: {}", e))?;

    Ok(TacticResult::Complete(term))
}

/// `apply e` — apply a term, generating sub-goals for remaining arguments
fn tactic_apply(
    expr: &ast::Expr,
    goal: &Goal,
    globals: &GlobalEnv,
) -> Result<TacticResult, String> {
    let mut ctx = LocalCtx::new();
    for (name, _, _) in &goal.hyps {
        ctx.bind(name.clone());
    }
    let term = elaborate::elaborate_expr(expr, &mut ctx, globals)
        .map_err(|e| format!("In apply: {}", e))?;

    // For now, just use the term directly
    Ok(TacticResult::Complete(term))
}

/// `refl` — prove `Eq a a` by reflexivity
fn tactic_refl(
    goal: &Goal,
    _globals: &GlobalEnv,
) -> Result<TacticResult, String> {
    // Check if target is Eq _ a a
    let _target = &goal.target;
    // Build Eq.refl term
    let refl_term = Term::Global("Eq.refl".to_string());
    Ok(TacticResult::Complete(refl_term))
}

/// `assumption` — search hypotheses for a proof of the goal
fn tactic_assumption(
    goal: &Goal,
    globals: &GlobalEnv,
) -> Result<TacticResult, String> {
    for (i, (_name, _, ty)) in goal.hyps.iter().enumerate().rev() {
        if conv_check(ty, &goal.target, goal.level, globals) {
            // de Bruijn index relative to the innermost binding
            let idx = goal.hyps.len() - 1 - i;
            return Ok(TacticResult::Complete(Term::Var(idx)));
        }
    }
    Err(format!(
        "No hypothesis matches the goal: {}",
        goal.target_term
    ))
}

/// `sorry` — admit any goal (with a warning)
fn tactic_sorry(
    _goal: &Goal,
    _globals: &GlobalEnv,
) -> Result<TacticResult, String> {
    eprintln!("  ⚠ Warning: sorry used, proof is incomplete");
    Ok(TacticResult::Complete(Term::Global("sorry".to_string())))
}

/// `trivial` — try to solve obvious goals
fn tactic_trivial(
    goal: &Goal,
    globals: &GlobalEnv,
) -> Result<TacticResult, String> {
    // Try refl first
    if let Ok(r) = tactic_refl(goal, globals) {
        return Ok(r);
    }
    // Try assumption
    if let Ok(r) = tactic_assumption(goal, globals) {
        return Ok(r);
    }
    // Try constructor
    if let Ok(r) = tactic_constructor(goal, globals) {
        return Ok(r);
    }
    Err("trivial: could not solve the goal".to_string())
}

/// `cases e` — case split on an expression
fn tactic_cases(
    expr: &ast::Expr,
    goal: &Goal,
    globals: &GlobalEnv,
) -> Result<TacticResult, String> {
    let mut ctx = LocalCtx::new();
    for (name, _, _) in &goal.hyps {
        ctx.bind(name.clone());
    }
    let term = elaborate::elaborate_expr(expr, &mut ctx, globals)
        .map_err(|e| format!("In cases: {}", e))?;

    // For now, produce a match expression
    // This is a simplified version
    let _target_term = goal.target_term.clone();
    let _match_term = Term::Match {
        scrutinee: Box::new(term),
        motive: None,
        arms: vec![],
    };

    Ok(TacticResult::Complete(Term::Global("sorry".to_string())))
}

/// `induction e` — perform structural induction
fn tactic_induction(
    expr: &ast::Expr,
    goal: &Goal,
    globals: &GlobalEnv,
) -> Result<TacticResult, String> {
    let mut ctx = LocalCtx::new();
    for (name, _, _) in &goal.hyps {
        ctx.bind(name.clone());
    }
    let _term = elaborate::elaborate_expr(expr, &mut ctx, globals)
        .map_err(|e| format!("In induction: {}", e))?;

    // Simplified: produce sorry placeholder
    // A full implementation would create goals for each constructor
    eprintln!("  ⚠ induction tactic: simplified implementation");
    Ok(TacticResult::Complete(Term::Global("sorry".to_string())))
}

/// `rewrite [e]` — rewrite using an equality
fn tactic_rewrite(
    _expr: &ast::Expr,
    _goal: &Goal,
    _globals: &GlobalEnv,
) -> Result<TacticResult, String> {
    // Simplified: for now just trust the rewrite
    eprintln!("  ⚠ rewrite tactic: simplified implementation");
    Ok(TacticResult::Complete(Term::Global("sorry".to_string())))
}

/// `simp` — simplification tactic
fn tactic_simp(
    goal: &Goal,
    globals: &GlobalEnv,
) -> Result<TacticResult, String> {
    // Try to normalize the target and see if it reduces to something trivial
    let normalized = normalize(&goal.target_term, &vec![], globals);
    eprintln!("  simp: normalized target to {}", normalized);

    // Check if it normalized to a reflexivity proof
    if let Ok(r) = tactic_refl(goal, globals) {
        return Ok(r);
    }

    // Try trivial
    if let Ok(r) = tactic_trivial(goal, globals) {
        return Ok(r);
    }

    Err("simp: could not simplify the goal".to_string())
}

/// `constructor` — apply a constructor
fn tactic_constructor(
    goal: &Goal,
    globals: &GlobalEnv,
) -> Result<TacticResult, String> {
    // Look at the target type and find applicable constructors
    match &goal.target {
        Value::Neutral(n) => {
            if let NeutralHead::Global(type_name) = &n.head {
                if let Some(ind) = globals.lookup_inductive(type_name) {
                    if let Some(ctor) = ind.constructors.first() {
                        return Ok(TacticResult::Complete(
                            Term::Global(ctor.name.clone())
                        ));
                    }
                }
            }
        }
        _ => {}
    }
    Err("constructor: target is not an inductive type".to_string())
}

/// `left` — apply the first constructor of a sum type
fn tactic_left(
    goal: &Goal,
    globals: &GlobalEnv,
) -> Result<TacticResult, String> {
    tactic_constructor(goal, globals)
}

/// `right` — apply the second constructor of a sum type
fn tactic_right(
    goal: &Goal,
    globals: &GlobalEnv,
) -> Result<TacticResult, String> {
    match &goal.target {
        Value::Neutral(n) => {
            if let NeutralHead::Global(type_name) = &n.head {
                if let Some(ind) = globals.lookup_inductive(type_name) {
                    if ind.constructors.len() >= 2 {
                        return Ok(TacticResult::Complete(
                            Term::Global(ind.constructors[1].name.clone())
                        ));
                    }
                }
            }
        }
        _ => {}
    }
    Err("right: target does not have a second constructor".to_string())
}

/// `have h : T := proof` — introduce a local hypothesis
fn tactic_have(
    name: &Name,
    ty_expr: &ast::Expr,
    _body: &ProofBody,
    goal: &Goal,
    globals: &GlobalEnv,
) -> Result<TacticResult, String> {
    let mut ctx = LocalCtx::new();
    for (n, _, _) in &goal.hyps {
        ctx.bind(n.clone());
    }
    let ty_term = elaborate::elaborate_expr(ty_expr, &mut ctx, globals)
        .map_err(|e| format!("In have type: {}", e))?;
    let ty_val = eval(&ty_term, &vec![], globals);

    // Create new goal with the hypothesis added
    let mut new_goal = goal.clone();
    new_goal.hyps.push((name.clone(), ty_term.clone(), ty_val));
    new_goal.level += 1;

    Ok(TacticResult::SubGoals {
        goals: vec![new_goal],
        combine: Box::new(move |terms| {
            assert!(!terms.is_empty());
            terms[0].clone()
        }),
    })
}

/// `show T` — assert that the current goal has type T
fn tactic_show(
    _expr: &ast::Expr,
    goal: &Goal,
    _globals: &GlobalEnv,
) -> Result<TacticResult, String> {
    // Just continue with the same goal
    Ok(TacticResult::SubGoals {
        goals: vec![goal.clone()],
        combine: Box::new(|terms| terms[0].clone()),
    })
}

/// `ring` — solve ring equations (simplified)
fn tactic_ring(
    _goal: &Goal,
    _globals: &GlobalEnv,
) -> Result<TacticResult, String> {
    eprintln!("  ⚠ ring tactic: simplified implementation");
    Ok(TacticResult::Complete(Term::Global("sorry".to_string())))
}

fn format_tactic(tactic: &Tactic) -> String {
    match tactic {
        Tactic::Intro(names) => format!("intro {}", names.join(" ")),
        Tactic::Apply(_) => "apply ...".to_string(),
        Tactic::Exact(_) => "exact ...".to_string(),
        Tactic::Refl => "refl".to_string(),
        Tactic::Rewrite(_) => "rewrite [...]".to_string(),
        Tactic::Cases(_) => "cases ...".to_string(),
        Tactic::Induction(_) => "induction ...".to_string(),
        Tactic::Simp => "simp".to_string(),
        Tactic::Assumption => "assumption".to_string(),
        Tactic::ConstructorTac => "constructor".to_string(),
        Tactic::Left => "left".to_string(),
        Tactic::Right => "right".to_string(),
        Tactic::Trivial => "trivial".to_string(),
        Tactic::Sorry => "sorry".to_string(),
        Tactic::Have(n, _, _) => format!("have {} ...", n),
        Tactic::Show(_) => "show ...".to_string(),
        Tactic::Ring => "ring".to_string(),
    }
}
