import AntSplice

namespace AntPlane
open AntInverse

def mark (f : Nat → Bool) (t : Nat) := f t ≠ f (t+104)
def gap (f : Nat → Bool) (a b : Nat) :=
  a<b ∧ mark f a ∧ mark f b ∧ ∀ j, a<j → j<b → ¬mark f j

/-- On the mismatch indicator, duplicating one period inserts precisely 104 zeroes. -/
theorem duplicate_marks (f : Nat → Bool) (s t : Nat) :
    mark (dup f s 104) t ↔
      (t<s ∧ mark f t) ∨ (s+104≤t ∧ mark f (t-104)) := by
  unfold mark dup
  by_cases he : t<s
  · simp [he,show t<s+104 by omega,show t+104<s+104 by omega,
      show ¬s+104≤t by omega]
  by_cases hm : t<s+104
  · simp [he,hm,show ¬t+104<s+104 by omega,show ¬s+104≤t by omega]
  · simp [he,hm,show ¬t+104<s+104 by omega,show s+104≤t by omega,
      show t-104+104=t by omega]

/-- Two marked endpoints and all the intervening unmarked indices can be
read from a single window of length b-a+105. -/
theorem witness_forces_gap {f g : Nat → Bool} {a b t : Nat}
    (h : gap f a b) (w : ∀ i, i<b-a+105 → g (t+i)=f (a+i)) :
    gap g t (t+(b-a)) := by
  obtain ⟨hab,ha,hb,mid⟩ := h
  have same (i : Nat) (hi : i≤b-a) : mark g (t+i) ↔ mark f (a+i) := by
    unfold mark
    rw [w i (by omega),show t+i+104=t+(i+104) by omega,w _ (by omega)]
    rw [Nat.add_assoc]
  refine ⟨by omega,?_,?_,?_⟩
  · simpa using (same 0 (by omega)).mpr (by simpa using ha)
  · apply (same _ (by omega)).mpr; rwa [show a+(b-a)=b by omega]
  · intro j hj hk
    have v : ¬mark g (t+(j-t)) := fun z => mid _ (by omega) (by omega) ((same (j-t) (by omega)).mp z)
    rwa [show t+(j-t)=j by omega] at v

/-- If [l,r+104) is periodic, changing its length by one period preserves all
windows through r-l+105, provided its pure extension occurs elsewhere in f. -/
theorem one_run_language {f : Nat → Bool} {s l r n : Nat}
    (ls : l≤s) (sr : s≤r) (per : ∀ i, l≤i → i<r → f (i+104)=f i)
    (pure : ∃ b, ∀ i, l≤i → i<r+208 → dup f s 104 i=f (b+(i-l)))
    (w : Nat → Bool) (hn : n≤r-l+105) :
    occurs (dup f s 104) w n ↔ occurs f w n := by
  have early (i : Nat) (hi : i<r+104) : dup f s 104 i=f i := by
    unfold dup; split
    · rfl
    · have e := per (i-104) (by omega) (by omega)
      simpa only [show i-104+104=i by omega] using e.symm
  have late (i : Nat) (hi : l+104≤i) : dup f s 104 i=f (i-104) := by
    unfold dup; split
    · have e := per (i-104) (by omega) (by omega)
      simpa only [show i-104+104=i by omega] using e
    · rfl
  constructor
  · rintro ⟨a,h⟩
    by_cases e : a+n≤r+104
    · exact ⟨a,fun i hi => (early (a+i) (by omega)).symm.trans (h i hi)⟩
    by_cases v : l+104≤a
    · refine ⟨a-104,fun i hi => ?_⟩
      have e' := h i hi
      rwa [late _ (by omega),show a+i-104=a-104+i by omega] at e'
    · obtain ⟨b,hp⟩ := pure
      refine ⟨b+(a-l),fun i hi => ?_⟩
      have e' := h i hi
      rwa [hp _ (by omega) (by omega),show b+(a+i-l)=b+(a-l)+i by omega] at e'
  · rintro ⟨a,h⟩
    by_cases e : a+n≤r+104
    · exact ⟨a,fun i hi => (early (a+i) (by omega)).trans (h i hi)⟩
    · refine ⟨a+104,fun i hi => ?_⟩
      rw [late _ (by omega),show a+104+i-104=a+i by omega]
      exact h i hi

#print axioms duplicate_marks
#print axioms witness_forces_gap
#print axioms one_run_language
end AntPlane
