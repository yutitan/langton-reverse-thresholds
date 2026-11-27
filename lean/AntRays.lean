import AntCoverage
import AntSplice

namespace AntPlane
open TwoBlack AntInverse

def readF (f : FState) (i : Nat) :=
  let a := frun i f
  a.black.contains a.pos

private theorem read_true (cells : List Pt) (s i : Nat) :
    readF (frun s (FState.init cells)) i = trace (initState cells) (s+i) := by
  unfold readF trace colour
  rw [←frun_add,←FState.init_toState cells,←frun_toState]
  rfl

def anchorB (f : FState) (s : Nat) :=
  let a := frun s f
  [45,46,55,56].any fun phase =>
    let b := 9977+phase
    let e := frun b f
    decide (b+208 ≤ 11000) && (List.range 208).all fun i =>
      readF e i == readF a (if i<104 then i else i-104)

private theorem anchor_sound (cells : List Pt) (s : Nat) (ok : anchorB (FState.init cells) s=true) :
    Anchored (trace (initState cells)) s := by
  obtain ⟨p,_,h⟩ := List.any_eq_true.mp ok
  obtain ⟨hb,hw⟩ := Bool.and_eq_true_iff.mp h
  refine ⟨9977+p,of_decide_eq_true hb,?_⟩
  intro i hi
  have eqn := beq_iff_eq.mp (List.all_eq_true.mp hw i (List.mem_range.mpr hi))
  change readF (frun (9977+p) (FState.init cells)) i =
    readF (frun s (FState.init cells)) (if i<104 then i else i-104) at eqn
  simp only [read_true] at eqn
  unfold cyclicAt
  split <;> simp_all

def familyB (p : Fam1 × Hint1) :=
  let cd := p.2.cd p.1
  decide (cd.J=1 ∨ cd.J=2) && decide (11000≤cd.m 1) &&
    (List.range cd.J).all (fun j => anchorB (FState.init (p.1.cells p.2.n)) (cd.m (j+1)))

private theorem all_families : level1Families.all familyB = true := by native_decide

theorem ray_language (p : Fam1 × Hint1) (hp : p∈level1Families)
    (k : Nat) (w : Nat → Bool) (n : Nat) (hn : n≤104) :
    occurs (trace (initState (p.1.cells (p.2.n+k)))) w n ↔
      occurs (trace (initState (p.1.cells p.2.n))) w n := by
  have ok := List.all_eq_true.mp all_families p hp
  simp only [familyB,Bool.and_eq_true,decide_eq_true_eq] at ok
  obtain ⟨⟨hj,ht⟩,hs⟩ := ok
  apply finite_language (List.all_eq_true.mp level1_checks p hp) hj _ k w n hn
  refine ⟨ht,fun j ha hb => ?_⟩
  have hj' : j-1 < (p.2.cd p.1).J := by omega
  have check := List.all_eq_true.mp hs (j-1) (List.mem_range.mpr hj')
  rw [show j-1+1=j by omega] at check
  exact anchor_sound _ _ check

theorem pull_word (p : Fam1 × Hint1) (hp : p∈level1Families) (k n t : Nat) (hn : n≤104) :
    ∃ b, word n (run t (initState (p.1.cells (p.2.n+k)))) =
      word n (run b (initState (p.1.cells p.2.n))) := by
  let x := initState (p.1.cells (p.2.n+k))
  let w := fun i => trace x (t+i)
  have occ : occurs (trace x) w n := ⟨t,fun _ _ => rfl⟩
  obtain ⟨b,hb⟩ := (ray_language p hp k w n hn).mp occ
  refine ⟨b,word_eq_of_colours _ _ _ (fun i hi => ?_)⟩
  rw [←run_add,←run_add]; exact (hb i hi).symm

end AntPlane
