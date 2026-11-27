import AntInverse
import AntPrepared

namespace AntPlane
open AntInverse TwoBlack
set_option maxRecDepth 8000

def trace (x : State) (t : Nat) := colour (run t x)

theorem corridor_letter {cd : CorridorData} {x y : State} (h : CorridorHyp cd x y)
    (q : Nat) (hq : q≤cd.J) (t : Nat) (ht : cd.InInt q t) :
    trace y (t+104*q) = trace x t := by
  have r := corridor cd x y h q hq t ht.1 (fun hlt => Nat.le_of_lt (ht.2 hlt))
  have b := h.c4 q hq t ht
  unfold Rq at r
  split at r
  · rename_i he
    exact congrArg Obs.c (obs_of_Rid r (by have := b.1 he; omega))
  · rename_i he
    exact congrArg Obs.c (obs_of_Rtr r (by have := b.2 (by omega); omega))

/- A complete doubled copy of this switch block occurs before time 11000. -/
def Anchored (f : Nat → Bool) (s : Nat) :=
  ∃ b, b+208 ≤ 11000 ∧ ∀ i<208, f (b+i) = cyclicAt f s 104 i

def Stable (cd : CorridorData) (x : State) :=
  11000 ≤ cd.m 1 ∧ ∀ j, 1≤j → j≤cd.J → Anchored (trace x) (cd.m j)

private theorem anchored_congr {f g : Nat → Bool} {s r : Nat}
    (early : ∀ i, i<11000 → g i=f i)
    (block : ∀ i, i<104 → g (r+i)=f (s+i)) (old : Anchored f s) : Anchored g r := by
  obtain ⟨b,hb,h⟩ := old
  refine ⟨b,hb,fun i hi => ?_⟩
  rw [early _ (by omega),h i hi]
  unfold cyclicAt
  split
  · exact (block _ (by omega)).symm
  · exact (block _ (by omega)).symm

private theorem anchored_factors {f : Nat → Bool} {s n : Nat} (a : Anchored f s)
    (w : Nat → Bool) (hn : n≤104) : occurs (dup f s 104) w n ↔ occurs f w n := by
  apply duplicate_factors _ _ _ _ _ hn
  obtain ⟨b,_,hb⟩ := a
  intro k hk
  exact ⟨b+k, fun i hi => by simpa only [Nat.add_assoc] using hb (k+i) (by omega)⟩

private theorem early_equal {cd : CorridorData} {x y : State} (h : CorridorHyp cd x y)
    {t : Nat} (he : t<cd.m 1+104) : trace y t=trace x t := by
  have a := corridor_letter h 0 (Nat.zero_le _) t ⟨by simp [CorridorData.start],fun _ => he⟩
  simpa using a

private theorem stable_succ {cd : CorridorData} {x y : State} (h : CorridorHyp cd x y)
    (old : Stable cd x) : Stable cd.succ y := by
  refine ⟨by have := old.1; simp [CorridorData.succ]; omega,?_⟩
  intro j hj hJ
  apply anchored_congr (f := trace x) (s := cd.m j)
  · intro t ht; exact early_equal h (by have := old.1; omega)
  · intro i hi
    have cell := corridor_letter h j hJ (cd.m j+i)
      ⟨by simp [CorridorData.start,show j≠0 by omega],fun hlt => by have := h.gap j hj hlt; omega⟩
    simp only [CorridorData.succ]
    rw [show cd.m j + 104*j+i=cd.m j+i+104*j by omega]; exact cell
  · exact old.2 j hj hJ

theorem one_splice {cd : CorridorData} {x y : State} (h : CorridorHyp cd x y)
    (hJ : cd.J=1) : trace y=dup (trace x) (cd.m 1) 104 := by
  funext t
  unfold dup
  split
  · rename_i he; exact early_equal h he
  · rename_i he
    have cell := corridor_letter h 1 (by omega) (t-104)
      ⟨by simp [CorridorData.start]; omega, fun hl => by omega⟩
    simpa only [Nat.mul_one,show t-104+104=t by omega] using cell

theorem two_splice {cd : CorridorData} {x y : State} (h : CorridorHyp cd x y)
    (hJ : cd.J=2) : trace y = dup (dup (trace x) (cd.m 1) 104) (cd.m 2+104) 104 := by
  have gap : cd.m 1 + 104 < cd.m 2 := h.gap 1 (by decide) (by omega)
  funext t
  by_cases a : t<cd.m 1+104
  · simpa only [dup,if_pos a,if_pos (show t<cd.m 2+104+104 by omega)] using early_equal h a
  by_cases b : t<cd.m 2+104+104
  · have cell := corridor_letter h 1 (by omega) (t-104)
      ⟨by simp [CorridorData.start]; omega,fun _ => by change t-104 < cd.m 2 + 104; omega⟩
    simpa only [dup,if_pos b,if_neg a,Nat.mul_one,show t-104+104=t by omega] using cell
  · have cell := corridor_letter h 2 (by omega) (t-208)
      ⟨by simp [CorridorData.start]; omega,fun hl => by omega⟩
    simpa only [dup,if_neg b,if_neg (show ¬t-104<cd.m 1+104 by omega),
      show t-104-104=t-208 by omega,show 104*2=208 by decide,show t-208+208=t by omega] using cell

theorem short_succ {cd : CorridorData} {x y : State} (h : CorridorHyp cd x y)
    (hJ : cd.J=1 ∨ cd.J=2) (st : Stable cd x) (w : Nat → Bool) (n : Nat) (hn : n≤104) :
    occurs (trace y) w n ↔ occurs (trace x) w n := by
  have first := st.2 1 (by decide) (by omega)
  rcases hJ with hj | hj
  · rw [one_splice h hj]
    exact anchored_factors first _ hn
  · rw [two_splice h hj]
    have gap : cd.m 1 + 104 < cd.m 2 := h.gap 1 (by decide) (by omega)
    have second : Anchored (dup (trace x) (cd.m 1) 104) (cd.m 2+104) := by
      apply anchored_congr (f := trace x) (s := cd.m 2)
      · intro i hi; simp only [dup,if_pos (show i<cd.m 1+104 by have := st.1; omega)]
      · intro i hi
        simp only [dup,if_neg (show ¬cd.m 2+104+i<cd.m 1+104 by omega),
          show cd.m 2+104+i-104=cd.m 2+i by omega]
      · exact st.2 2 (by decide) (by omega)
    exact (anchored_factors second _ hn).trans (anchored_factors first _ hn)

theorem finite_language {F : Fam1} {H : Hint1} (ok : check1 F H=true)
    (hj : (H.cd F).J=1 ∨ (H.cd F).J=2) (base : Stable (H.cd F) (initState (F.cells H.n)))
    (k : Nat) (w : Nat → Bool) (n : Nat) (hn : n≤104) :
    occurs (trace (initState (F.cells (H.n+k)))) w n ↔
      occurs (trace (initState (F.cells H.n))) w n := by
  let cd := H.cd F
  let X := fun r => initState (F.cells (H.n+r))
  have prep := prepared_of_check F H ok
  have J (r : Nat) : (cd.iter r).J=cd.J := by
    induction r with
    | zero => rfl
    | succ r ih => exact ih
  have aux (r : Nat) : Stable (cd.iter r) (X r) ∧
      (occurs (trace (X r)) w n ↔ occurs (trace (X 0)) w n) := by
    induction r with
    | zero => exact ⟨base,Iff.rfl⟩
    | succ r ih =>
      have rel := prep r
      exact ⟨stable_succ rel ih.1,
        (short_succ rel (by rw [show ((H.cd F).iter r).J=cd.J from J r]; exact hj)
          ih.1 w n hn).trans ih.2⟩
  exact (aux k).2

end AntPlane
