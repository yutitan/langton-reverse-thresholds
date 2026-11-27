import AntSharpBase
namespace AntSharp
open AntPlane AntInverse TwoBlack

set_option maxRecDepth 1000000 in
theorem rays_checked : level1Families.all wholeB=true := by native_decide

set_option maxRecDepth 1000000 in
/-- Thresholds, in the order of the upstream 22 families. -/
theorem threshold_table :
    level1Families.map (fun p => width p+104) = cutTable.map Prod.fst := by native_decide

/-- Every pair of distinct ordered depths on one ray has exactly this first
distinguishing length. Occurrence quantifies over the entire infinite run. -/
theorem ray_threshold_exact (p : Fam1 × Hint1) (hp : p∈level1Families)
    (k d : Nat) (hd : 0<d) :
    (∀ n, n≤width p+104+104*k → ∀ w,
      occurs (trace (X p (k+d))) w n ↔ occurs (trace (X p k)) w n) ∧
    (∃ w, occurs (trace (X p k)) w (width p+104+104*k+1) ∧
      ¬occurs (trace (X p (k+d))) w (width p+104+104*k+1)) := by
  have b := checked_plan p (List.all_eq_true.mp rays_checked p hp)
  have e := exact_of_plan p hp _ b.1 b.2 k d hd
  rwa [show width p+104+104*k=width p+104*k+104 by omega,
    show width p+104*k+104+1=width p+104*k+105 by omega]

#print axioms threshold_table
#print axioms ray_threshold_exact
end AntSharp
