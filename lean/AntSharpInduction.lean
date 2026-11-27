import AntSharpWords
import AntRays
namespace AntSharp
open AntPlane AntInverse TwoBlack

def Classified (f : Nat → Bool) (u v : Zone) :=
  ∀ a b, gap f a b → b-a≤71 ∨ (a=u.a ∧ b=u.b) ∨ (a=v.a ∧ b=v.b)

theorem class_shift {f : Nat → Bool} {u v z : Zone} (hc : Classified f u v)
    (hz : Valid f z) (member : z=u ∨ z=v) :
    Classified (dup f z.s 104) (u.trans z.s) (v.trans z.s) := by
  intro t e h
  obtain ⟨a,b,rfl,rfl,hg⟩ := (gap_image _ _ _ _).mp h
  have lift (y : Zone) (eqn : a=y.a ∧ b=y.b) :
      push z.s a=(y.trans z.s).a ∧ push z.s b=(y.trans z.s).b := by
    rw [eqn.1,eqn.2]; exact ⟨rfl,rfl⟩
  rcases hc a b hg with small | ueq | veq
  · by_cases cross : a<z.s ∧ z.s≤b
    · have ez := gap_unique hg hz.1 cross.1 cross.2 hz.2.1 hz.2.2.1
      rcases member with rfl | rfl
      · exact Or.inr (Or.inl (lift _ ez))
      · exact Or.inr (Or.inr (lift _ ez))
    · left; unfold push; split <;> split <;> have := hg.1 <;> omega
  · exact Or.inr (Or.inl (lift _ ueq))
  · exact Or.inr (Or.inr (lift _ veq))

def Plan (cd : CorridorData) (f : Nat → Bool) (M : Nat) :=
  ∃ u v : Zone, Valid f u ∧ Valid f v ∧ Classified f u v ∧ min u.size v.size=M ∧
  u.s=cd.m 1 ∧ ((cd.J=1 ∧ v=u) ∨ (cd.J=2 ∧ v.s=cd.m 2 ∧ u.b<v.a))

theorem plan_step {cd : CorridorData} {x y : State} {M : Nat} (h : CorridorHyp cd x y)
    (pl : Plan cd (trace x) M) :
    Plan cd.succ (trace y) (M+104) ∧ ∀ n, n≤M+104 → ∀ w,
      occurs (trace y) w n ↔ occurs (trace x) w n := by
  obtain ⟨u,v,hu,hv,hc,hm,us,one | two⟩ := pl
  · obtain ⟨hj,eqv⟩ := one
    subst v
    rw [one_splice h hj,←us]
    have a := hu.2.1
    have b := hu.2.2.1
    have mn : u.size=M := by simpa using hm
    have size : (u.trans u.s).size=u.size+104 := by
      simp [Zone.trans,Zone.size,push,a,show ¬u.b<u.s by omega]; omega
    refine ⟨⟨_,_,valid_trans hu u.s,valid_trans hu u.s,class_shift hc hu (Or.inl rfl),?_,?_,Or.inl ⟨hj,rfl⟩⟩,?_⟩
    · simp [size,mn]
    · simp [Zone.trans,push,CorridorData.succ,us]
    · intro n hn w; exact zone_language hu w n (by omega)
  · obtain ⟨hj,vs,sep⟩ := two
    have a := hu.2.1
    have b := hu.2.2.1
    have c := hv.2.1
    have d := hv.2.2.1
    let U := u.trans u.s
    let V := v.trans u.s
    have Vc : V.s=v.s+104 := by simp [V,Zone.trans,push,show ¬v.s<u.s by omega]
    rw [two_splice h hj,←us,←vs,←Vc]
    have hU := valid_trans hu u.s
    have hV := valid_trans hv u.s
    have cls := class_shift hc hu (Or.inl rfl)
    have Va : V.a=v.a+104 := by simp [V,Zone.trans,push,show ¬v.a<u.s by omega]
    have Vb : V.b=v.b+104 := by simp [V,Zone.trans,push,show ¬v.b<u.s by omega]
    have Ua : U.a=u.a := by simp [U,Zone.trans,push,a]
    have Us : U.s=u.s+104 := by simp [U,Zone.trans,push]
    have Ub : U.b=u.b+104 := by simp [U,Zone.trans,push,show ¬u.b<u.s by omega]
    have lowU : (U.trans V.s).size=u.size+104 := by
      simp [Zone.size,Zone.trans,push,Ua,Ub,Vc,show u.a<v.s+104 by omega,show u.b+104<v.s+104 by omega]; omega
    have lowV : (V.trans V.s).size=v.size+104 := by
      simp [Zone.size,Zone.trans,push,Va,Vb,Vc,show v.a+104<v.s+104 by omega,show ¬v.b+104<v.s+104 by omega]; omega
    refine ⟨⟨U.trans V.s,V.trans V.s,valid_trans hU V.s,valid_trans hV V.s,
      class_shift cls hV (Or.inr rfl),?_,?_,Or.inr ⟨hj,?_,?_⟩⟩,?_⟩
    · rw [lowU,lowV]; omega
    · simp [Zone.trans,push,Us,Vc,CorridorData.succ,us]; omega
    · simp [Zone.trans,push,Vc,CorridorData.succ,vs]
    · simp [Zone.trans,push,Ub,Va,Vc,show u.b+104<v.s+104 by omega,show v.a+104<v.s+104 by omega]; omega
    · intro n hn w
      have eqs : V.size=v.size := by simp [Zone.size,Va,Vb]
      exact (zone_language hV w n (by change n≤V.size+104; omega)).trans (zone_language hu w n (by omega))

def X (p : Fam1 × Hint1) (k : Nat) := initState (p.1.cells (p.2.n+k))

theorem exact_of_plan (p : Fam1 × Hint1) (hp : p∈level1Families) (M : Nat)
    (big : 71<M) (base : Plan (p.2.cd p.1) (trace (X p 0)) M)
    (k d : Nat) (hd : 0<d) :
    (∀ n, n≤M+104*k+104 → ∀ w, occurs (trace (X p (k+d))) w n ↔ occurs (trace (X p k)) w n) ∧
    (∃ w, occurs (trace (X p k)) w (M+104*k+105) ∧ ¬occurs (trace (X p (k+d))) w (M+104*k+105)) := by
  let cd := p.2.cd p.1
  have pre := prepared_of_check p.1 p.2 (List.all_eq_true.mp level1_checks p hp)
  have plans (j : Nat) : Plan (cd.iter j) (trace (X p j)) (M+104*j) := by
    induction j with
    | zero => exact base
    | succ j ih => simpa only [Nat.mul_succ,Nat.add_assoc] using (plan_step (pre j) ih).1
  constructor
  · intro n hn w
    clear hd
    induction d with
    | zero => exact Iff.rfl
    | succ d ih =>
      exact ((plan_step (pre (k+d)) (plans (k+d))).2 n (by omega) w).trans ih
  · obtain ⟨u,v,hu,hv,_,mn,_⟩ := plans k
    obtain ⟨U,V,_,_,deep,bigM,_⟩ := plans (k+d)
    have emit (z : Zone) (hz : Valid (trace (X p k)) z) (sz : z.size=M+104*k) :
        ∃ w, occurs (trace (X p k)) w (M+104*k+105) ∧ ¬occurs (trace (X p (k+d))) w (M+104*k+105) := by
      refine ⟨fun i => trace (X p k) (z.a+i),⟨z.a,fun _ _ => rfl⟩,?_⟩
      rintro ⟨j,hit⟩
      have dis : z.b-z.a=M+104*k := sz
      have imp := witness_forces_gap hz.1 (t:=j) (g:=trace (X p (k+d))) (fun i hi => hit i (by omega))
      rcases deep _ _ imp with small | a | a
      · omega
      · have sU : U.size=z.b-z.a := by unfold Zone.size; omega
        omega
      · have sV : V.size=z.b-z.a := by unfold Zone.size; omega
        omega
    by_cases e : u.size≤v.size
    · exact emit u hu (by omega)
    · exact emit v hv (by omega)
end AntSharp
