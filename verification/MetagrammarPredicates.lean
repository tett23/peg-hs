import ConcreteTables
import GhcPredicates

namespace PegHs.MetagrammarPredicates
open SemanticPredicates

abbrev Site := String × Bool × String

-- The tables retain the Haskell expression exactly, including its padding.
def classifySite (s : Site) := kinds.find? (fun k => " " ++ spelling k ++ " " == s.2.2)

def supported (table : Array Site) := table.all fun s => (classifySite s).isSome

theorem invariant1_all_sites : supported MetaTerminal1.predicateSites = true ∧
    supported MetaTerminal2.predicateSites = true := by decide +kernel

def runSite (site : Site) (env : Env) : Option Bool :=
  (classifySite site).map fun k => eval GhcPredicates.classes k env == site.2.1

theorem invariant1_site_result (site : Site) (env : Env) :
    runSite site env = some true ↔ ∃ k, classifySite site = some k ∧
      (Holds GhcPredicates.classes env k ↔ site.2.1 = true) := by
  cases h : classifySite site with
  | none => simp [runSite, h]
  | some k =>
    cases hp : site.2.1 <;> cases hv : eval GhcPredicates.classes k env <;>
      simp [runSite, h, hp, hv, ← invariant1_eval_iff]

theorem invariant1_defined {table : Array Site} (checked : supported table = true)
    (i : Fin table.size) (env : Env) : ∃ b, runSite table[i] env = some b := by
  have ok : (classifySite table[i]).isSome = true := Array.all_eq_true.mp checked i.val i.isLt
  generalize eq : table[i] = site at ok ⊢
  cases h : classifySite site with
  | none => simp [h] at ok
  | some k => simp [runSite, h]

end PegHs.MetagrammarPredicates
