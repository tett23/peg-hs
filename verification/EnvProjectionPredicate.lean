import EnvProjection
import PredicateBindings

namespace PegHs.EnvProjection
open PegHs.EnvironmentEval

theorem actual_predicate_projection (kind : SemanticPredicates.Kind) (env : Env) :
    PredicateBindings.predicateEnv kind env =
      predicateProjection (PredicateBindings.captureName kind) env := rfl

def PredicateReads (left right : Env) (kind : SemanticPredicates.Kind) : Prop :=
  if kind = .depth then left.depth = right.depth
  else (PredicateBindings.predicateEnv kind left).captured =
    (PredicateBindings.predicateEnv kind right).captured

theorem actual_predicate_only_reads {left right : Env}
    (classes : SemanticPredicates.Classes) (kind : SemanticPredicates.Kind)
    (reads : PredicateReads left right kind) :
    SemanticPredicates.eval classes kind (PredicateBindings.predicateEnv kind left) =
      SemanticPredicates.eval classes kind (PredicateBindings.predicateEnv kind right) := by
  cases kind <;> simp [PredicateReads, PredicateBindings.predicateEnv,
    SemanticPredicates.eval] at reads ⊢ <;> simp [reads] <;> rfl

theorem actual_predicate_noninterference {left right : Env}
    (same : ObsEq left right) (classes : SemanticPredicates.Classes)
    (kind : SemanticPredicates.Kind) :
    SemanticPredicates.eval classes kind (PredicateBindings.predicateEnv kind left) =
      SemanticPredicates.eval classes kind (PredicateBindings.predicateEnv kind right) := by
  rw [actual_predicate_projection, actual_predicate_projection]
  exact semanticPredicate_congr same classes kind _

#print axioms actual_predicate_noninterference
#print axioms actual_predicate_only_reads

end PegHs.EnvProjection
