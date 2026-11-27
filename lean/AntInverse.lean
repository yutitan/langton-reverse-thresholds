import TwoBlack.Parent0

namespace AntInverse
open TwoBlack

/- Duplicate a period-length block of an infinite word. An old factor survives
and a new short factor crossing the join is cyclic inside the copied block. -/
def dup {α} (f : Nat → α) (s p t : Nat) := if t < s+p then f t else f (t-p)
def occurs {α} (f w : Nat → α) (n : Nat) := ∃ a, ∀ i < n, f (a+i) = w i
def cyclicAt {α} (f : Nat → α) (s p u : Nat) :=
  if u < p then f (s+u) else f (s+(u-p))

theorem duplicate_factors {α} (f w : Nat → α) (s p n : Nat) (hn : n ≤ p)
    (tail : ∀ k < p, ∃ b, ∀ i < n, f (b+i) = cyclicAt f s p (k+i)) :
    occurs (dup f s p) w n ↔ occurs f w n := by
  constructor
  · rintro ⟨a, ha⟩
    by_cases left : a+n ≤ s+p
    · exact ⟨a, fun i hi => by simpa [dup, show a+i<s+p by omega] using ha i hi⟩
    by_cases right : s+p ≤ a
    · refine ⟨a-p, fun i hi => ?_⟩
      simpa [dup, show ¬ a+i<s+p by omega, show a+i-p=a-p+i by omega] using ha i hi
    · obtain ⟨b,hb⟩ := tail (a-s) (by omega)
      refine ⟨b, fun i hi => ?_⟩
      rw [hb i hi, ← ha i hi]
      unfold cyclicAt dup
      split <;> split <;> first | congr 1 <;> omega | omega
  · rintro ⟨a, ha⟩
    by_cases early : a<s
    · exact ⟨a, fun i hi => by simpa [dup, show a+i<s+p by omega] using ha i hi⟩
    · refine ⟨a+p,fun i hi => ?_⟩
      simpa [dup, show ¬a+p+i<s+p by omega, show a+p+i-p=a+i by omega] using ha i hi

def word : Nat → State → List Bool
  | 0, _ => []
  | n+1, s => (s.black s.pos) :: word n (step s)
def fword : Nat → FState → List Bool
  | 0, _ => []
  | n+1, f => (f.black.contains f.pos) :: fword n f.step
theorem word_correct (n) (f : FState) : fword n f = word n f.toState := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp [fword, word, ih, FState.step_toState]

def blank := FState.init []
def forward := fword 104 (frun 9977 blank)
def inverse (phase length : Nat) : List Bool :=
  (List.range length).map fun i => !(forward[103-(phase+i)%104]!)
def matchAt (cells : List Pt) (t phase length : Nat) : Prop :=
  word length (run t (initState cells)) = inverse phase length

theorem replay (cells : List Pt) (t p n : Nat)
    (h : fword n (frun t (FState.init cells)) = inverse p n) : matchAt cells t p n := by
  simpa [matchAt,word_correct,frun_toState,FState.init_toState] using h

theorem zero32 : matchAt [] 1041 4 32 := replay _ _ _ _ (by native_decide)

def forbidden (len : Nat) := (List.range 104).map (fun p => inverse p len)
def avoids (len : Nat) (pats : List (List Bool)) : Nat → FState → Bool
  | 0, _ => true
  | n+1, f => !(pats.contains (fword len f)) && avoids len pats n f.step

theorem avoids_sound (len n : Nat) (f : FState) (h : avoids len (forbidden len) n f = true) (t : Nat)
    (ht : t<n) (p : Fin 104) : fword len (frun t f) ≠ inverse p len := by
  induction n generalizing f t with
  | zero => omega
  | succ n ih =>
    have checks := Bool.and_eq_true_iff.mp h
    cases t with
    | zero =>
      intro eqn
      have mem : inverse p len ∈ forbidden len :=
        List.mem_map.mpr ⟨p.val,List.mem_range.mpr p.isLt,rfl⟩
      rw [←eqn] at mem
      simp at checks
      exact checks.1 mem
    | succ t => exact ih f.step checks.2 t (by omega)

def colour (s : State) := s.black s.pos
theorem periodic_colour (cells : List Pt) (s c j : Nat)
    (hc : certAt (frun s (FState.init cells)) = true) :
    colour (run (s+c*104+j) (initState cells)) =
    colour (run (s+j) (initState cells)) := by
  let entry := frun s (FState.init cells)
  obtain ⟨u,A,hu,hag,hin⟩ := certAt_sound entry hc
  have eqs : entry.toState = run s (initState cells) := by
    simp [entry,frun_toState,FState.init_toState]
  have compat : Agree (fun z => dot u z > A) u
      (run s (initState cells)) (run (s+104) (initState cells)) := by
    simpa only [frun_toState,eqs,run_add] using hag
  have inside (i : Nat) (hi : i<104) :
      dot u (run (s+i) (initState cells)).pos > A := by
    have ri := hin i hi
    change dot u (frun i entry).toState.pos > A at ri
    simpa only [frun_toState,eqs,run_add] using ri
  exact congrArg Obs.c (halfplane_obs (initState cells) _ u s 104 (by decide)
    (stdDrift_dot_pos hu · A) compat inside c j)

theorem word_eq_of_colours (n : Nat) (s s' : State)
    (h : ∀ i<n, colour (run i s) = colour (run i s')) : word n s = word n s' := by
  induction n generalizing s s' with
  | zero => rfl
  | succ n ih =>
    have first := h 0 (by omega)
    have rest := ih (step s) (step s') (fun i hi => by
      simpa [←run_succ'] using h (i+1) (by omega))
    exact List.cons.injEq _ _ _ _ |>.mpr ⟨first,rest⟩

theorem upper_of_checked_prefix (cells : List Pt) (s len : Nat)
    (hc : certAt (frun s (FState.init cells)) = true)
    (hfinite : ∀ a, a<s+104 → ∀ p : Fin 104,
      word len (run a (initState cells)) ≠ inverse p len)
    (t : Nat) (p : Fin 104) : ¬ matchAt cells t p len := by
  have finite (a : Nat) (ha : a<s+104) :
      word len (run a (initState cells)) ≠ inverse p len := by
    exact hfinite a ha p
  by_cases early : t<s+104
  · exact finite t early
  let k := (t-s)/104
  let r := (t-s)%104
  have hr : r<104 := Nat.mod_lt _ (by decide)
  have ht : t=s+k*104+r := by dsimp [k,r]; omega
  have eqn : word len (run t (initState cells)) = word len (run (s+r) (initState cells)) := by
    apply word_eq_of_colours
    intro i _
    rw [←run_add, ←run_add, ht]
    simpa only [Nat.add_assoc] using periodic_colour cells s k (r+i) hc
  exact fun h => finite (s+r) (by omega) (eqn.symm.trans h)

theorem upper_sound (cells : List Pt) (s len : Nat)
    (hc : certAt (frun s (FState.init cells)) = true)
    (hfinite : avoids len (forbidden len) (s+104) (FState.init cells) = true) :
    ∀ t (p : Fin 104), ¬ matchAt cells t p len := by
  apply upper_of_checked_prefix cells s len hc
  intro a ha p
  simpa [word_correct,frun_toState,FState.init_toState] using avoids_sound len _ _ hfinite a ha p

theorem blank_no33 : ∀ t (p : Fin 104), ¬ matchAt [] t p 33 :=
  upper_sound [] 10504 33 (by native_decide) (by native_decide)
theorem witness_no59 : ∀ t (p : Fin 104), ¬ matchAt [⟨-30,-2⟩] t p 59 :=
  upper_sound [⟨-30,-2⟩] 37960 59 (by native_decide) (by native_decide)
theorem witness_no88 : ∀ t (p : Fin 104), ¬ matchAt [⟨24,-14⟩,⟨-11,6⟩] t p 88 :=
  upper_sound [⟨24,-14⟩,⟨-11,6⟩] 22256 88 (by native_decide) (by native_decide)
theorem one58 : matchAt [⟨-30,-2⟩] 29393 6 58 := replay _ _ _ _ (by native_decide)
theorem two87 : matchAt [⟨24,-14⟩,⟨-11,6⟩] 14770 92 87 :=
  replay _ _ _ _ (by native_decide)
theorem three88 : matchAt [⟨-86,-46⟩,⟨-63,-43⟩,⟨-22,-14⟩] 214688 90 88 :=
  replay _ _ _ _ (by native_decide)
def seed11 : List Pt := [⟨1,-1⟩,⟨-3,-3⟩,⟨-3,-1⟩,⟨-4,-8⟩,⟨-4,-1⟩,⟨-6,-8⟩,
  ⟨-6,-5⟩,⟨-6,-3⟩,⟨-6,-2⟩,⟨-6,-1⟩,⟨-7,-6⟩]
def seed20 : List Pt := [⟨1,-1⟩,⟨-2,-5⟩,⟨-3,-5⟩,⟨-3,-4⟩,⟨-3,-3⟩,⟨-3,-1⟩,⟨-4,-4⟩,
  ⟨-4,-1⟩,⟨-4,0⟩,⟨-5,-6⟩,⟨-6,-8⟩,⟨-6,-5⟩,⟨-6,-3⟩,⟨-6,-2⟩,⟨-6,-1⟩,
  ⟨-7,1⟩,⟨-8,-4⟩,⟨-8,-1⟩,⟨-8,0⟩,⟨-8,1⟩]
theorem eleven101 : matchAt seed11 221 77 101 := replay _ _ _ _ (by native_decide)
theorem twelve110 : matchAt (⟨-7,-5⟩::seed11) 221 77 110 := replay _ _ _ _ (by native_decide)
theorem twenty208 : seed20.Nodup ∧ seed20.length=20 ∧ matchAt seed20 209 73 208 :=
  ⟨by decide,by decide,replay _ _ _ _ (by native_decide)⟩

/- Initial black coordinates required by first visits, in a frame with fixed
origin. Keeping the first head occurrence overrides every later reading. -/
def needs (p : Pt) (d : Dir) : List Bool → List Pt
  | [] => []
  | b::w =>
    let next := turn b d
    let rest := (needs (p+next.vec) next w).filter (· != p)
    if b then p::rest else rest

theorem need_sound (w : List Bool) (s : State) (origin off : Pt)
    (pose : s.pos = origin + off) (hw : word w.length s = w) :
    ∀ z ∈ needs off s.dir w, s.black (origin+z) = true := by
  induction w generalizing s off with
  | nil => simp [needs]
  | cons b ws ih =>
    have h := List.cons.inj hw
    have hb : s.black s.pos = b := h.1
    have pose' : (step s).pos = origin + (off+(turn b s.dir).vec) := by
      rw [step_pos,hb,pose,Pt.add_assoc]
    have tail := ih (step s) _ pose' h.2
    intro z hz
    by_cases eq : z=off
    · subst z
      rw [←pose,hb]
      cases b <;> simp_all [needs]
    · have mem : z ∈ needs (off+(turn b s.dir).vec) (turn b s.dir) ws := by
        cases b <;> simpa [needs, eq] using hz
      have ne : origin+z ≠ s.pos := by
        rw [pose]; intro he
        apply eq
        exact Pt.ext' (by have hx := congrArg Pt.x he; simp at hx; omega)
          (by have hy := congrArg Pt.y he; simp at hy; omega)
      have mem' : z ∈ needs (off+(turn b s.dir).vec) (step s).dir ws := by
        simpa [step_dir,hb] using mem
      simpa [step_black,ne] using tail z mem'

def enough (d : Dir) (p : Fin 104) :=
  let q := needs Pt.zero d (inverse p 104)
  q.Nodup ∧ 23 ≤ q.length

theorem all_phases (d : Dir) : ∀ p : Fin 104, enough d p := by
  cases d <;> unfold enough <;> native_decide

theorem immediate23 (s : State) (p : Fin 104) (h : word 104 s = inverse p 104) :
    ∃ offsets : List Pt, offsets.Nodup ∧ 23 ≤ offsets.length ∧
      ∀ z ∈ offsets, s.black (s.pos+z) = true := by
  refine ⟨_,(all_phases s.dir p).1,(all_phases s.dir p).2,?_⟩
  apply need_sound _ s s.pos Pt.zero (Pt.add_zero _).symm
  simpa [inverse] using h

def minSeed := needs Pt.zero .N (inverse 67 104)
theorem sharp23 : minSeed.Nodup ∧ minSeed.length = 23 ∧ matchAt minSeed 0 67 104 :=
  ⟨by native_decide,by native_decide,replay _ _ _ _ (by native_decide)⟩

/- Accounting for exact inverse periods. 'inside' and 'outside' refer to
the same fixed set of missing parallel lanes, cut by the perpendicular wakes. -/
theorem exact_supply (K a E h beforeInside afterInside beforeOutside afterOutside : Nat)
    (loss : a*K + afterInside + afterOutside ≤ beforeInside + beforeOutside)
    (outsideBound : beforeOutside ≤ E) (insideBound : beforeInside ≤ 22*h) :
    a*K ≤ E+22*h := by omega

abbrev Lane := Int × Bool
def wake : List Lane := [(0,false),(0,true),(1,false),(2,true),(3,true),(4,false),
  (5,true),(6,true),(8,false),(9,false),(10,false),(10,true)]
def positive : List Lane := [(0,false),(0,true),(6,true),(8,false),(10,false),(10,true)]
def weight (z : Lane) : Int :=
  if z.1 < 0 ∨ z.1 > 10 then 0 else
  if z ∈ positive then 1 else if z ∈ wake then 0 else -1
structure Track where
  offset : Fin 10
  halfturn : Bool
  swap : Bool
def bulk (o : Fin 10) (halfturn swap : Bool) : Int :=
  (wake.map (fun (r,b) =>
    weight ((if halfturn then 10-r else r) + 2*(o.val:Int)-9,b ^^ swap))).sum
theorem target_six : (wake.map weight).sum = 6 := by decide
theorem one_bulk : ∀ (o : Fin 10) (h s : Bool), bulk o h s ≤ 0 := by native_decide
theorem any_many_bulk (xs : List Track) :
    (xs.map (fun x => bulk x.offset x.halfturn x.swap)).sum ≤ 0 := by
  induction xs with
  | nil => decide
  | cons a xs ih =>
    simp only [List.map_cons,List.sum_cons]
    have h := one_bulk a.offset a.halfturn a.swap
    omega

def potential (s : State) : List (Pt × Int) → Int
  | [] => 0
  | (z,w)::xs => (if s.black z then w else 0) + potential s xs
def coefficient (q : Pt) : List (Pt × Int) → Int
  | [] => 0
  | (z,w)::xs => (if z=q then w else 0)+coefficient q xs
def signedStep (s : State) (xs : List (Pt × Int)) :=
  if s.black s.pos then -(coefficient s.pos xs) else coefficient s.pos xs
theorem potential_step (s : State) (xs : List (Pt × Int)) :
    potential (step s) xs = potential s xs + signedStep s xs := by
  induction xs with
  | nil => simp [potential,signedStep,coefficient]
  | cons a xs ih =>
    rcases a with ⟨z,w⟩
    by_cases hz : z=s.pos <;> cases hb : s.black s.pos <;>
      simp [potential, ih, signedStep, coefficient, step_black,hz,hb] <;> omega
def flux : Nat → State → List (Pt × Int) → Int
  | 0, _, _ => 0
  | n+1, s, xs => signedStep s xs + flux n (step s) xs
theorem potential_run (n : Nat) (s : State) (xs : List (Pt × Int)) :
    potential (run n s) xs = potential s xs + flux n s xs := by
  induction n generalizing s with
  | zero => simp [flux]
  | succ n ih => rw [run_succ',ih,potential_step,flux]; omega

end AntInverse
