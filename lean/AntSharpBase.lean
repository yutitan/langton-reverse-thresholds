import AntSharpInduction
import AntGapData
namespace AntSharp
open AntPlane AntInverse TwoBlack

def tape (p : Fam1 × Hint1) :=
  (fword (p.2.s+104) (FState.init (p.1.cells p.2.n))).toArray

def model (p : Fam1 × Hint1) (t : Nat) : Bool :=
  (tape p)[if t<p.2.s then t else p.2.s+(t-p.2.s)%104]!

theorem get_word (n : Nat) (f : FState) (i : Nat) (hi : i<n) :
    (fword n f)[i]! = colour (run i f.toState) := by
  induction n generalizing f i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa only [fword,List.getElem!_cons_succ,run_succ',FState.step_toState] using ih f.step i (by omega)

theorem model_eq (p : Fam1 × Hint1) (hc : certAt (frun p.2.s (FState.init (p.1.cells p.2.n)))=true) :
    model p = trace (X p 0) := by
  funext t
  unfold model tape
  rw [List.getElem!_toArray]
  by_cases ht : t<p.2.s
  · simp only [if_pos ht,get_word _ _ _ (show t<p.2.s+104 by omega),FState.init_toState]
    rfl
  · let j := (t-p.2.s)%104
    let c := (t-p.2.s)/104
    have jh : j<104 := Nat.mod_lt _ (by decide)
    have th : t=p.2.s+c*104+j := by dsimp [c,j]; omega
    simp only [if_neg ht]
    change (fword _ _)[p.2.s+j]! = _
    rw [get_word _ _ _ (by omega),FState.init_toState]
    exact (th ▸ periodic_colour (p.1.cells p.2.n) p.2.s c j hc).symm

def bit (a : Array Bool) (s t : Nat) :=
  a[if t<s then t else s+(t-s)%104]!
def flagged (f : Nat → Bool) (t : Nat) := f t != f (t+104)
theorem flag_iff (f : Nat → Bool) (t : Nat) : flagged f t=true ↔ mark f t := by
  simp [mark,flagged]

def zoneFor (f : Nat → Bool) (T s : Nat) : Zone :=
  let a := ((List.range s).filter (flagged f)).getLastD 0
  let b := (((List.range (T-s)).find? fun i => flagged f (s+i)).getD 0)+s
  ⟨a,s,b⟩

def zoneB (arr : Array Bool) (T : Nat) (z : Zone) : Bool :=
  let f := bit arr T
  decide (z.a<z.s ∧ z.s≤z.b) && flagged f z.a && flagged f z.b &&
  (List.range 104).any fun ph =>
    (List.range (z.b+104-(z.a+1))).all fun i =>
      let t := z.a+1+i
      f t == f (T+(t+ph)%104)

theorem zone_ok (arr : Array Bool) (T : Nat) (z : Zone) (h : zoneB arr T z=true) :
    Valid (bit arr T) z := by
  let f := bit arr T
  simp only [zoneB,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨low,high⟩,ha⟩,hb⟩,phase⟩ := h
  obtain ⟨ph,_,good⟩ := List.any_eq_true.mp phase
  let v := fun t => f (T+(t+ph)%104)
  have per (i : Nat) : v (i+104)=v i := by
    dsimp [v]; rw [show (i+104+ph)%104=(i+ph)%104 by omega]
  have loc (i : Nat) (hi : z.a<i) (he : i<z.b+104) : f i=v i := by
    have chk := List.all_eq_true.mp good (i-(z.a+1)) (List.mem_range.mpr (by omega))
    exact beq_iff_eq.mp (by simpa only [show z.a+1+(i-(z.a+1))=i by omega] using chk)
  refine ⟨⟨by omega,(flag_iff _ _).mp ha,(flag_iff _ _).mp hb,?_⟩,low,high,v,per,?_,loc⟩
  · intro j hj hJ
    unfold mark
    change ¬ f j ≠ f (j+104)
    rw [loc _ hj (by omega),loc _ (by omega) (by omega),per]
    simp
  · intro L
    refine ⟨T+104*L+ph,by omega,?_⟩
    intro i; dsimp [v,f,bit]
    simp only [if_neg (show ¬T+104*L+ph+i<T by omega),
      if_neg (show ¬T+(i+ph)%104<T by omega)]
    congr 2 <;> omega

def classB (f : Nat → Bool) (T : Nat) (u v : Zone) : Bool :=
  let last := ((List.range T).filter (flagged f)).getLastD 0
  (List.range T).all fun i => !flagged f i ||
    (decide (i≤last) && (decide (i=last ∨ i=u.a ∨ i=v.a) ||
      (List.range 71).any fun j => flagged f (i+1+j)))

theorem class_ok (arr : Array Bool) (T : Nat) (u v : Zone)
    (hu : Valid (bit arr T) u) (hv : Valid (bit arr T) v)
    (ok : classB (bit arr T) T u v=true) : Classified (bit arr T) u v := by
  let f := bit arr T
  have ltT (i : Nat) (m : mark f i) : i<T := by
    by_cases e : i<T
    · exact e
    exfalso
    apply m
    simp only [f,bit,if_neg (show ¬i<T by omega),if_neg (show ¬i+104<T by omega)]
    congr 2 <;> omega
  intro a b h
  have ca := List.all_eq_true.mp ok a (List.mem_range.mpr (ltT _ h.2.1))
  have cb := List.all_eq_true.mp ok b (List.mem_range.mpr (ltT _ h.2.2.1))
  simp only [(flag_iff _ _).mpr h.2.1,(flag_iff _ _).mpr h.2.2.1,Bool.not_true,Bool.false_or,
    Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at ca cb
  rcases ca.2 with (e | e | e) | near
  · have := cb.1; have := h.1; omega
  · right; left; exact gap_unique h hu.1 (s:=a+1) (by omega) (by have := h.1; omega)
      (by omega) (by have := hu.1.1; omega)
  · right; right; exact gap_unique h hv.1 (s:=a+1) (by omega) (by have := h.1; omega)
      (by omega) (by have := hv.1.1; omega)
  · obtain ⟨j,hj,hm⟩ := List.any_eq_true.mp near
    have bound := List.mem_range.mp hj
    have z := (flag_iff _ _).mp hm
    left
    by_cases e : b-a≤71
    · exact e
    exfalso
    exact h.2.2.2 _ (by omega) (by omega) z

def pairZones (p : Fam1 × Hint1) :=
  let f := bit (tape p) p.2.s
  let cd := p.2.cd p.1
  let u := zoneFor f p.2.s (cd.m 1)
  let v := if cd.J=1 then u else zoneFor f p.2.s (cd.m 2)
  (u,v)

def width (p : Fam1 × Hint1) :=
  min (pairZones p).1.size (pairZones p).2.size

def wholeB (p : Fam1 × Hint1) :=
  let arr := tape p
  let T := p.2.s
  let (u,v) := pairZones p
  let cd := p.2.cd p.1
  certAt (frun T (FState.init (p.1.cells p.2.n))) &&
    zoneB arr T u && zoneB arr T v && classB (bit arr T) T u v &&
    decide (71<width p) && decide (u.s=cd.m 1 ∧
      ((cd.J=1 ∧ v=u) ∨ (cd.J=2 ∧ v.s=cd.m 2 ∧ u.b<v.a)))

theorem checked_plan (p : Fam1 × Hint1) (ok : wholeB p=true) :
    71<width p ∧ Plan (p.2.cd p.1) (trace (X p 0)) (width p) := by
  simp only [wholeB,Bool.and_eq_true,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨⟨cert,zu⟩,zv⟩,cl⟩,big⟩,tim⟩ := ok
  rw [←model_eq p cert]
  exact ⟨big,(pairZones p).1,(pairZones p).2,zone_ok _ _ _ zu,zone_ok _ _ _ zv,
    class_ok _ _ _ _ (zone_ok _ _ _ zu) (zone_ok _ _ _ zv) cl,rfl,tim⟩
end AntSharp
