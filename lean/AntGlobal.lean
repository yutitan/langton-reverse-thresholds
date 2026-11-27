import AntRays
import AntFinite

namespace AntPlane
open TwoBlack AntInverse

/- Use the 2,388 previously certified sites as an existing dependency. -/
private theorem same_seen (n : Nat) (f : FState) : seen n f = positions n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp only [seen,positions,ih]

private theorem extra_checked : extra.all checkOne = true := by
  set_option maxRecDepth 1000000 in native_decide

def headB (p : Fam1 × Hint1) := match p.1.cells p.2.n with
  | [z] => checkOne z
  | _ => false

private theorem heads_checked : level1Families.all headB = true := by
  set_option maxRecDepth 1000000 in native_decide

private theorem head_upper (p : Fam1 × Hint1) (hp : p∈level1Families) (t : Nat) (q : Fin 104) :
    ¬matchAt (p.1.cells p.2.n) t q 59 := by
  have ok := List.all_eq_true.mp heads_checked p hp
  dsimp only [headB] at ok
  split at ok
  · rename_i z eqn
    rw [eqn]; exact checkOne_sound _ ok t q
  · contradiction

private theorem blank_upper : ∀ t (q : Fin 104), ¬ matchAt [] t q 59 :=
  upper_sound [] 10504 59 (by native_decide) (by native_decide)

/-- An arbitrary location for the single initial black cell, and an arbitrary time and phase. -/
theorem one_black_no59 (z : Pt) (t : Nat) (q : Fin 104) : ¬matchAt [z] t q 59 := by
  by_cases touch : ∃ a, (run a (initState [])).pos = z
  · obtain ⟨a,ha⟩ := touch
    have cov := visit_cover a
    dsimp only at cov
    rw [ha] at cov
    rcases cov with old | extraSite | ⟨p,hp,k,eqn⟩
    · apply finite_one_upper z _ t q
      simpa only [early,representatives,same_seen] using old
    · exact checkOne_sound _ (List.all_eq_true.mp extra_checked _ extraSite) t q
    · obtain ⟨b,eqw⟩ := pull_word p hp k 59 t (by decide)
      rw [eqn] at eqw
      exact fun h => head_upper p hp b q (eqw.symm.trans h)
  · have hu := unread_word (z := z) (fun j he => touch ⟨j,he⟩) t 59
    exact fun h => blank_upper t q (hu.symm.trans h)

theorem one_black_exact :
    (∃ z : Pt, ∃ t : Nat, ∃ p : Fin 104, matchAt [z] t p 58) ∧
    (∀ z t (p : Fin 104), ¬matchAt [z] t p 59) :=
  ⟨⟨⟨-30,-2⟩,29393,⟨6,by decide⟩,one58⟩,one_black_no59⟩

#print axioms one_black_exact
end AntPlane
