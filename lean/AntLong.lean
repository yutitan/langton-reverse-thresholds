import AntRays

namespace AntPlane
open AntInverse TwoBlack

/- The k periods to the left of s are recorded letter by letter. -/
def Buffer (f : Nat → Bool) (s k : Nat) :=
  104*k ≤ s ∧ ∀ a, s ≤ a+104*k → a<s → f (a+104) = f a

private theorem buffer_dup {f : Nat → Bool} {s k : Nat} (h : Buffer f s k) :
    Buffer (dup f s 104) (s+104) (k+1) := by
  obtain ⟨h0,h⟩ := h
  refine ⟨by omega,fun a lo hi => ?_⟩
  simp only [dup,if_pos hi]
  split
  · exact h _ (by omega) (by omega)
  · rw [show a+104-104=a by omega]

private theorem move_buffer {f : Nat → Bool} {s r k : Nat} (h : Buffer f r k)
    (gap : s+104+104*k ≤ r) : Buffer (dup f s 104) (r+104) k := by
  refine ⟨by omega,fun a lo hi => ?_⟩
  have ha : ¬a<s+104 := by omega
  simp only [dup,if_neg ha,if_neg (show ¬a+104<s+104 by omega)]
  have old := h.2 (a-104) (by omega) (by omega)
  simpa only [show a+104-104=a by omega,show a-104+104=a by omega] using old

private theorem keep_buffer {f : Nat → Bool} {s r k : Nat} (h : Buffer f s k)
    (le : s≤r) : Buffer (dup f r 104) s k := by
  refine ⟨h.1,fun a lo hi => ?_⟩
  simp only [dup,if_pos (show a<r+104 by omega),if_pos (show a+104<r+104 by omega)]
  exact h.2 a lo hi

/- Long windows still agree once there are enough copies. Windows reaching the
right flank can then shift 104 places using only the repeated part on the left. -/
private theorem buffered_factors {f : Nat → Bool} {s k n : Nat} (h : Buffer f s k)
    (w : Nat → Bool) (hn : n≤104*k+1) : occurs (dup f s 104) w n ↔ occurs f w n := by
  have h0 := h.1
  have late (i : Nat) (hi : s+104 ≤ i+104*k) : dup f s 104 i = f (i-104) := by
    unfold dup
    split
    · have eqn := h.2 (i-104) (by omega) (by omega)
      simpa only [show i-104+104=i by omega] using eqn
    · rfl
  constructor
  · rintro ⟨a,ha⟩
    by_cases e : a+n≤s+104
    · exact ⟨a,fun i hi => by simpa only [dup,if_pos (show a+i<s+104 by omega)] using ha i hi⟩
    · refine ⟨a-104,fun i hi => ?_⟩
      have eqn := ha i hi
      rwa [late _ (by omega),show a+i-104=a-104+i by omega] at eqn
  · rintro ⟨a,ha⟩
    by_cases e : a+n≤s+104
    · exact ⟨a,fun i hi => by simpa only [dup,if_pos (show a+i<s+104 by omega)] using ha i hi⟩
    · refine ⟨a+104,fun i hi => ?_⟩
      rw [late _ (by omega),show a+104+i-104=a+i by omega]
      exact ha i hi

def Buffers (cd : CorridorData) (x : State) (k : Nat) :=
  Buffer (trace x) (cd.m 1) k ∧
    (cd.J=2 → cd.m 1+104+104*k ≤ cd.m 2 ∧ Buffer (trace x) (cd.m 2) k)

private theorem next_buffers {cd : CorridorData} {x y : State} {k : Nat}
    (h : CorridorHyp cd x y) (hj : cd.J=1 ∨ cd.J=2) (old : Buffers cd x k) :
    Buffers cd.succ y (k+1) := by
  rcases hj with j | j
  · refine ⟨?_,fun hj => by change cd.J=2 at hj; omega⟩
    rw [one_splice h j]
    exact buffer_dup old.1
  · obtain ⟨gap,second⟩ := old.2 j
    have m1 : cd.succ.m 1=cd.m 1+104 := rfl
    have m2 : cd.succ.m 2=cd.m 2+104+104 := by simp [CorridorData.succ]
    constructor
    · rw [two_splice h j,m1]
      exact keep_buffer (buffer_dup old.1) (by omega)
    · intro _
      rw [m1,m2,two_splice h j]
      exact ⟨by omega,buffer_dup (move_buffer second gap)⟩

private theorem buffered_succ {cd : CorridorData} {x y : State} {k n : Nat}
    (h : CorridorHyp cd x y) (hj : cd.J=1 ∨ cd.J=2) (buf : Buffers cd x k)
    (w : Nat → Bool) (hn : n≤104*k+1) :
    occurs (trace y) w n ↔ occurs (trace x) w n := by
  rcases hj with j | j
  · rw [one_splice h j]; exact buffered_factors buf.1 w hn
  · rw [two_splice h j]
    obtain ⟨gap,second⟩ := buf.2 j
    exact (buffered_factors (move_buffer second gap) w hn).trans (buffered_factors buf.1 w hn)

/-- For every word length n, all ray members at depths H.n + k + d have
the same n-letter factors as depth H.n + k if n ≤ 104*k+1. -/
theorem long_ray_language (p : Fam1 × Hint1) (hp : p∈level1Families)
    (k d n : Nat) (w : Nat → Bool) (hn : n≤104*k+1) :
    occurs (trace (initState (p.1.cells (p.2.n+(k+d))))) w n ↔
      occurs (trace (initState (p.1.cells (p.2.n+k)))) w n := by
  let cd := p.2.cd p.1
  let X := fun r => initState (p.1.cells (p.2.n+r))
  have prep := prepared_of_check p.1 p.2 (List.all_eq_true.mp level1_checks p hp)
  have table : level1Families.all (fun z => decide ((z.2.cd z.1).J=1 ∨ (z.2.cd z.1).J=2))=true := by
    native_decide
  have j0 : cd.J=1 ∨ cd.J=2 := of_decide_eq_true (List.all_eq_true.mp table p hp)
  have J (r : Nat) : (cd.iter r).J=cd.J := by
    induction r with
    | zero => rfl
    | succ r ih => exact ih
  have bounds (r : Nat) : Buffers (cd.iter r) (X r) r := by
    induction r with
    | zero =>
      have vac (s : Nat) : Buffer (trace (X 0)) s 0 := ⟨by omega,fun i hi hl => by omega⟩
      refine ⟨vac _,fun hj => ⟨?_,vac _⟩⟩
      change cd.J=2 at hj
      have g : cd.m 1+104 < cd.m 2 := (prep 0).gap 1 (by decide) (by change 1<cd.J; omega)
      change cd.m 1+104+104*0≤cd.m 2; omega
    | succ r ih => exact next_buffers (prep r) (by change (cd.iter r).J=1 ∨ (cd.iter r).J=2; rw [J]; exact j0) ih
  induction d with
  | zero => exact Iff.rfl
  | succ d ih =>
    have ys := buffered_succ (prep (k+d))
      (by change (cd.iter (k+d)).J=1 ∨ (cd.iter (k+d)).J=2; rw [J]; exact j0)
      (bounds (k+d)) w (n := n) (by omega)
    exact ys.trans ih

#print axioms long_ray_language
end AntPlane
