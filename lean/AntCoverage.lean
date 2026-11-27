import AntInverse
import TwoBlack.Level1Data

namespace AntPlane
open TwoBlack AntInverse

def seen : Nat → FState → List Pt
  | 0, _ => []
  | n+1,f => f.pos :: seen n f.step

theorem seen_at (n : Nat) (f : FState) (t : Nat) (ht : t<n) :
    (frun t f).pos ∈ seen n f := by
  induction n generalizing f t with
  | zero => omega
  | succ n ih =>
    cases t with
    | zero => simp [seen,frun]
    | succ t => exact List.mem_cons_of_mem _ (ih f.step t (by omega))

def early := (seen 14768 blank).eraseDups
def extra := ((seen 208 (frun 14768 blank)).eraseDups).filter (fun z => !(early.contains z))
def rayTest (z : Pt) := level1Families.any fun p =>
  (List.range 20).any fun k => p.1.cells (p.2.n+k) == [z]

def Ray (z : Pt) := ∃ p ∈ level1Families, ∃ k : Nat, p.1.cells (p.2.n+k) = [z]
theorem rayTest_sound {z : Pt} (h : rayTest z = true) : Ray z := by
  obtain ⟨p,hp,hk⟩ := List.any_eq_true.mp h
  obtain ⟨k,_,he⟩ := List.any_eq_true.mp hk
  exact ⟨p,hp,k,beq_iff_eq.mp he⟩

private theorem uniform_drift : level1Families.all (fun p =>
    p.1.δ == Diag.mm && p.1.near.isEmpty) = true := by native_decide

theorem ray_shift {z : Pt} (h : Ray z) (c : Nat) : Ray (z + Pt.smul c Diag.mm.v) := by
  obtain ⟨p,hp,k,hk⟩ := h
  obtain ⟨hd,hn⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp uniform_drift p hp)
  have d := beq_iff_eq.mp hd
  have n := List.isEmpty_iff.mp hn
  refine ⟨p,hp,k+c,?_⟩
  have eqn := congrArg (List.map (fun b : Pt => b + Pt.smul (c : Int) Diag.mm.v)) hk
  simp only [Fam1.cells,n,List.nil_append,List.map_map,List.map_cons,List.map_nil] at eqn ⊢
  rw [←eqn]
  apply List.map_congr_left
  intro b _
  simp [d,Pt.add_assoc,Pt.smul_add,Int.add_assoc]

private theorem checkedAgree (f g : FState) (v : Pt) (a : Int)
    (hpos : g.pos=f.pos+v) (hdir : g.dir=f.dir)
    (hb : agreeB (fun z => decide (dot v z>a)) v f.black g.black=true) :
    Agree (fun z => dot v z>a) v f.toState g.toState := by
  refine ⟨hpos,hdir,fun z hz => ?_⟩
  exact agreeB_sound hb z (by simpa only [decide_eq_true_eq] using hz)

set_option maxRecDepth 50000 in
private theorem blank_drift (c j : Nat) :
    (run (10504+c*104+j) (initState [])).pos =
    (run (10504+j) (initState [])).pos + Pt.smul c Diag.mm.v := by
  let f := frun 10504 blank
  let G := fun z => decide (dot Diag.mm.v z > 49)
  have chk : (((frun 104 f).pos == f.pos + Diag.mm.v) &&
      ((frun 104 f).dir == f.dir) && agreeB G Diag.mm.v f.black (frun 104 f).black &&
      readsB G f 104) = true := by native_decide
  simp only [Bool.and_eq_true,beq_iff_eq] at chk
  obtain ⟨⟨⟨hp,hd⟩,ha⟩,hr⟩ := chk
  have fx : f.toState = run 10504 (initState []) := by
    rw [←FState.init_toState]; exact frun_toState _ _
  have ag : Agree (fun z => dot Diag.mm.v z > 49) Diag.mm.v f.toState (frun 104 f).toState :=
    checkedAgree f (frun 104 f) Diag.mm.v 49 hp hd ha
  rw [frun_toState 104 f,fx,←run_add] at ag
  have inside (i : Nat) (hi : i<104) : dot Diag.mm.v (run (10504+i) (initState [])).pos > 49 := by
    have rd := readsB_sound hr i hi
    rw [run_add,←fx,←frun_toState]; simpa [G] using rd
  exact congrArg Obs.pos (halfplane_obs _ _ Diag.mm.v 10504 104 (by decide)
    (fun z => stdDrift_dot_pos (by simp [StdDrift, Diag.v] : StdDrift Diag.mm.v) z 49) ag inside c j)

set_option maxRecDepth 1000000 in
theorem extra_count : extra.length = 44 := by native_decide
set_option maxRecDepth 1000000 in
private theorem bridge : (seen 520 (frun 14768 blank)).all
    (fun z => early.contains z || extra.contains z || rayTest z) = true := by native_decide
private theorem block : (seen 104 (frun 15288 blank)).all rayTest = true := by native_decide

private theorem blank_pos (t : Nat) : (run t (initState [])).pos = (frun t blank).pos := by
  rw [←FState.init_toState,←frun_toState]; rfl

theorem visit_cover (t : Nat) :
    let z := (run t (initState [])).pos
    z ∈ early ∨ z ∈ extra ∨ Ray z := by
  dsimp only
  by_cases h : t < 14768
  · left; rw [blank_pos]; exact List.mem_eraseDups.mpr (seen_at _ _ t h)
  by_cases h' : t < 15288
  · obtain ⟨j,hj,rfl⟩ : ∃ j, j<520 ∧ t=14768+j := ⟨t-14768,by omega,by omega⟩
    rw [blank_pos,frun_add]
    have b := List.all_eq_true.mp bridge _ (seen_at _ _ j hj)
    simp only [Bool.or_eq_true,List.contains_iff_mem] at b
    rcases b with (he | he) | hr
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr (rayTest_sound hr))
  · right; right
    obtain ⟨c,j,hj,ht⟩ : ∃ c j, j<104 ∧ t=10504+c*104+(4784+j) :=
      ⟨(t-15288)/104,(t-15288)%104,Nat.mod_lt _ (by decide),by omega⟩
    rw [ht,blank_drift,show 10504+(4784+j)=15288+j by omega]
    apply ray_shift
    rw [blank_pos,frun_add]
    exact rayTest_sound (List.all_eq_true.mp block _ (seen_at _ _ j hj))

theorem unread_word {z : Pt} (hn : ∀ t, (run t (initState [])).pos ≠ z) (t n : Nat) :
    word n (run t (initState [z])) = word n (run t (initState [])) := by
  have init : Agree (· ≠ z) Pt.zero (initState []) (initState [z]) := by
    refine ⟨rfl,rfl,?_⟩
    intro q hq
    simp [initState,Pt.add_zero,hq]
  apply word_eq_of_colours
  intro i _
  rw [←run_add,←run_add]
  have rel := agree_run (t+i) init (fun j _ => hn j)
  unfold colour
  rw [rel.1,rel.2.2 _ (hn (t+i))]

end AntPlane
