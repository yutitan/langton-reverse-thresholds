import AntInverse

namespace AntPlane
open AntInverse TwoBlack

def nearCell : Pt := ⟨-113,-94⟩
def farCell : Pt := ⟨-115,-96⟩
def distinguishing := fword 4979 (frun 66086 (FState.init [nearCell]))

private theorem first_letters (a b : Nat) (f : FState) (h : a≤b) :
    (fword b f).take a = fword a f := by
  induction a generalizing b f with
  | zero => rfl
  | succ a ih =>
    cases b with
    | zero => omega
    | succ b => simp only [fword,List.take_succ_cons]; rw [ih _ _ (by omega)]

/- Filter candidate positions with 32 letters. Every surviving candidate is
compared letter-for-letter with the entire 4,979-letter word. -/
def scanLost (w pre : List Bool) : Nat → FState → Bool
  | 0, _ => true
  | n+1, f => ((fword 32 f != pre) || (fword 4979 f != w)) && scanLost w pre n f.step

private theorem scan_sound (w : List Bool) (n : Nat) (f : FState)
    (ok : scanLost w (w.take 32) n f=true) (t : Nat) (ht : t<n) :
    fword 4979 (frun t f) ≠ w := by
  induction n generalizing f t with
  | zero => omega
  | succ n ih =>
    obtain ⟨test,rest⟩ := Bool.and_eq_true_iff.mp ok
    cases t with
    | zero =>
      change fword 4979 f≠w
      intro eqn
      have pref := first_letters 32 4979 f (by decide)
      rw [eqn] at pref
      simp [eqn,pref] at test
    | succ t => exact ih _ rest t (by omega)

private theorem still_present : word 4979 (run 66086 (initState [nearCell])) = distinguishing := by
  rw [distinguishing,word_correct,frun_toState,FState.init_toState]

private theorem cert_far : certAt (frun 80392 (FState.init [farCell])) = true := by native_decide
set_option maxRecDepth 1000000 in
private theorem checked : scanLost distinguishing (distinguishing.take 32) (80392+104)
    (FState.init [farCell])=true := by native_decide

theorem lost_far (t : Nat) : word 4979 (run t (initState [farCell])) ≠ distinguishing := by
  have short (b : Nat) (hb : b<80392+104) :
      word 4979 (run b (initState [farCell])) ≠ distinguishing := by
    simpa only [word_correct,frun_toState,FState.init_toState] using
      scan_sound distinguishing _ _ checked b hb
  by_cases he : t<80392+104
  · exact short t he
  · let c := (t-80392)/104
    let j := (t-80392)%104
    have hj : j<104 := Nat.mod_lt _ (by decide)
    have ht : t=80392+c*104+j := by dsimp [c,j]; omega
    have eqw : word 4979 (run t (initState [farCell])) =
        word 4979 (run (80392+j) (initState [farCell])) := by
      apply word_eq_of_colours
      intro i _
      rw [←run_add,←run_add,ht]
      simpa only [Nat.add_assoc] using periodic_colour [farCell] 80392 c (j+i) cert_far
    exact fun eqn => short (80392+j) (by omega) (eqw.symm.trans eqn)

theorem lost_4979 : ∃ w, word 4979 (run 66086 (initState [nearCell]))=w ∧
    ∀ t, word 4979 (run t (initState [farCell]))≠w := ⟨distinguishing,still_present,lost_far⟩

#print axioms lost_4979
end AntPlane
