import AntInverse
namespace AntInverse
open TwoBlack

inductive Trie where | dead | hit | fork (l r : Trie)
def tails (b : Bool) (ws : List (List Bool)) :=
  ws.filterMap fun w => match w with
    | [] => none
    | h::t => if h=b then some t else none
def trie : Nat → List (List Bool) → Trie
  | _, [] => .dead
  | 0, _::_ => .hit
  | n+1, w::ws => .fork (trie n (tails false (w::ws))) (trie n (tails true (w::ws)))
def found : Trie → List Bool → Bool
  | .dead, _ => false
  | .hit, _ => true
  | .fork _ _, [] => false
  | .fork l r, b::xs => if b then found r xs else found l xs
theorem trie_hit (n : Nat) (ws : List (List Bool)) (pat rest : List Bool)
    (h : pat∈ws) (hl : pat.length=n) : found (trie n ws) (pat++rest)=true := by
  induction n generalizing pat ws with
  | zero => cases ws with
    | nil => simp at h
    | cons w ws => rfl
  | succ n ih =>
    cases ws with
    | nil => simp at h
    | cons w ws =>
      cases pat with
      | nil => simp at hl
      | cons b xs =>
        have mem : xs∈tails b (w::ws) := by
          apply List.mem_filterMap.mpr
          exact ⟨b::xs,h,by simp⟩
        have eqn := ih _ _ mem (by simpa using hl)
        cases b <;> exact eqn

def clear : Nat → Trie → List Bool → Bool
  | 0, _, _ => true
  | _+1, _, [] => false
  | n+1, tr, a::xs => !(found tr (a::xs)) && clear n tr xs
theorem clear_drop (n : Nat) (tr : Trie) (xs : List Bool) (ok : clear n tr xs=true)
    (i : Nat) (hi : i<n) : found tr (xs.drop i)=false := by
  induction n generalizing xs i with
  | zero => omega
  | succ n ih =>
    cases xs with
    | nil => simp [clear] at ok
    | cons h t =>
      have checks := Bool.and_eq_true_iff.mp ok
      cases i with
      | zero => simpa using checks.1
      | succ i => exact ih _ checks.2 _ (by omega)

theorem fword_append (n m : Nat) (f : FState) :
    fword (n+m) f = fword n f ++ fword m (frun n f) := by
  induction n generalizing f with
  | zero => simp [fword,frun]
  | succ n ih => simp [Nat.succ_add,fword,frun,ih]

theorem fword_length (n : Nat) (f : FState) : (fword n f).length=n := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp [fword,ih]

def trie59 := trie 59 (forbidden 59)
def fast59 (n : Nat) (f : FState) := clear n trie59 (fword (n+59) f)
theorem fast59_sound (n : Nat) (f : FState) (ok : fast59 n f=true) (i : Nat) (hi : i<n)
    (p : Fin 104) : fword 59 (frun i f) ≠ inverse p 59 := by
  intro eqn
  have no := clear_drop n trie59 _ ok i hi
  have a : n+59=i+(59+(n-i)) := by omega
  rw [a,fword_append i, List.drop_left' (fword_length i f), fword_append 59, eqn] at no
  have mem : inverse p 59∈forbidden 59 :=
    List.mem_map.mpr ⟨p.val,List.mem_range.mpr p.isLt,rfl⟩
  have yes := trie_hit 59 (forbidden 59) (inverse p 59)
    (fword (n-i) (frun 59 (frun i f))) mem (by simp [inverse])
  exact Bool.noConfusion (no.symm.trans yes)

/- Probe every 832 steps. Success carries a concrete time with its certificate. -/
def findCut : Nat → FState → Option Nat
  | 0, _ => none
  | k+1, f => if certAt f then some 0 else (findCut k (frun 832 f)).map (832+·)
theorem findCut_sound (k : Nat) (f : FState) (s : Nat) (h : findCut k f=some s) :
    certAt (frun s f)=true := by
  induction k generalizing f s with
  | zero => simp [findCut] at h
  | succ k ih =>
    unfold findCut at h
    split at h
    · rename_i ok
      cases h; exact ok
    · cases he : findCut k (frun 832 f) with
      | none => simp [he] at h
      | some n =>
        simp [he] at h
        subst s; rw [frun_add]; exact ih _ _ he
def checkOne (z : Pt) :=
  let f := FState.init [z]
  match findCut 240 f with
  | none => false
  | some s => fast59 (s+104) f
set_option maxRecDepth 1000000 in
theorem checkOne_sound (z : Pt) (ok : checkOne z=true) :
    ∀ t (p : Fin 104), ¬ matchAt [z] t p 59 := by
  dsimp only [checkOne] at ok
  split at ok
  · contradiction
  · rename_i x s heq
    apply upper_of_checked_prefix [z] s 59 (findCut_sound _ _ _ heq)
    intro a ha p
    simpa [word_correct,frun_toState,FState.init_toState] using fast59_sound _ _ ok a ha p

def positions : Nat → FState → List Pt
  | 0, _ => []
  | n+1,f => f.pos :: positions n f.step
def representatives := (positions 14768 blank).eraseDups
set_option maxRecDepth 1000000 in
theorem representatives_count : representatives.length=2388 := by native_decide
set_option maxRecDepth 1000000 in
theorem representatives_checked : representatives.all checkOne = true := by native_decide
theorem finite_one_upper (z : Pt) (hz : z∈representatives) :
    ∀ t (p : Fin 104), ¬matchAt [z] t p 59 :=
  checkOne_sound z (List.all_eq_true.mp representatives_checked z hz)

end AntInverse
