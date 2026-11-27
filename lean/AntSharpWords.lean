import AntMarkers
namespace AntSharp
open AntInverse AntPlane

def push (s t : Nat) := if t<s then t else t+104

theorem push_lt (s a b : Nat) : push s a < push s b ↔ a<b := by
  unfold push; split <;> split <;> omega

theorem mark_image (f : Nat → Bool) (s t : Nat) :
    mark (dup f s 104) t ↔ ∃ a, t=push s a ∧ mark f a := by
  rw [duplicate_marks]
  constructor
  · rintro (⟨ht,h⟩ | ⟨ht,h⟩)
    · exact ⟨t,by simp [push,ht],h⟩
    · exact ⟨t-104,by simp [push,show ¬t-104<s by omega]; omega,h⟩
  · rintro ⟨a,rfl,h⟩
    by_cases e : a<s
    · exact Or.inl (by simpa [push,e] using And.intro e h)
    · right; simp [push,e,h]; omega

theorem gap_image (f : Nat → Bool) (s t u : Nat) :
    gap (dup f s 104) t u ↔ ∃ a b, t=push s a ∧ u=push s b ∧ gap f a b := by
  constructor
  · rintro ⟨hlt,ht,hu,hmid⟩
    obtain ⟨a,rfl,ha⟩ := (mark_image _ _ _).mp ht
    obtain ⟨b,rfl,hb⟩ := (mark_image _ _ _).mp hu
    refine ⟨a,b,rfl,rfl,(push_lt _ _ _).mp hlt,ha,hb,?_⟩
    intro j h1 h2 h3
    exact hmid _ ((push_lt _ _ _).mpr h1) ((push_lt _ _ _).mpr h2)
      ((mark_image _ _ _).mpr ⟨j,rfl,h3⟩)
  · rintro ⟨a,b,rfl,rfl,hlt,ha,hb,hm⟩
    refine ⟨(push_lt _ _ _).mpr hlt,(mark_image _ _ _).mpr ⟨a,rfl,ha⟩,
      (mark_image _ _ _).mpr ⟨b,rfl,hb⟩,?_⟩
    intro j h1 h2 h3
    obtain ⟨c,rfl,hc⟩ := (mark_image _ _ _).mp h3
    exact hm _ ((push_lt _ _ _).mp h1) ((push_lt _ _ _).mp h2) hc

theorem gap_unique {f : Nat → Bool} {a b c d s : Nat} (h : gap f a b) (g : gap f c d)
    (h1 : a<s) (h2 : s≤b) (h3 : c<s) (h4 : s≤d) : a=c ∧ b=d := by
  have za : a=c := by
    rcases Nat.lt_trichotomy a c with H|H|H
    · exact False.elim (h.2.2.2 c H (by omega) g.2.1)
    · exact H
    · exact False.elim (g.2.2.2 a H (by omega) h.2.1)
  refine ⟨za,?_⟩
  rcases Nat.lt_trichotomy b d with H|H|H
  · exact False.elim (g.2.2.2 b (by omega) H h.2.2.1)
  · exact H
  · exact False.elim (h.2.2.2 d (by omega) H g.2.2.1)

structure Zone where
  a : Nat
  s : Nat
  b : Nat
deriving DecidableEq, Repr

def Zone.trans (z : Zone) (s : Nat) : Zone := ⟨push s z.a, push s z.s, push s z.b⟩
def Zone.size (z : Zone) := z.b-z.a
def Echo (f v : Nat → Bool) := ∀ L, ∃ o, L≤o ∧ ∀ i, f (o+i)=v i
def Valid (f : Nat → Bool) (z : Zone) :=
  gap f z.a z.b ∧ z.a<z.s ∧ z.s≤z.b ∧ ∃ v : Nat → Bool,
  (∀ i, v (i+104)=v i) ∧ Echo f v ∧ ∀ i, z.a<i → i<z.b+104 → f i=v i

private theorem inside_shift {f v : Nat → Bool} {a b s : Nat}
    (localEq : ∀ i, a<i → i<b+104 → f i=v i) (per : ∀ i, v (i+104)=v i)
    (i : Nat) (lo : push s a<i) (hi : i<push s b+104) : dup f s 104 i=v i := by
  unfold push at lo hi
  unfold dup; split
  · apply localEq <;> split at lo <;> split at hi <;> omega
  · rename_i he
    have p := per (i-104)
    rw [show i-104+104=i by omega] at p
    rw [p]; apply localEq <;> split at lo <;> split at hi <;> omega

theorem valid_trans {f : Nat → Bool} {z : Zone} (h : Valid f z) (s : Nat) :
    Valid (dup f s 104) (z.trans s) := by
  obtain ⟨gap0,ls,sr,v,per,echo,loc⟩ := h
  refine ⟨(gap_image _ _ _ _).mpr ⟨_,_,rfl,rfl,gap0⟩,(push_lt _ _ _).mpr ls,
    Nat.le_of_not_gt (fun e => Nat.not_lt_of_ge sr ((push_lt _ _ _).mp e)),v,per,?_,?_⟩
  · intro L
    obtain ⟨o,ho,he⟩ := echo (L+s+104)
    refine ⟨o+104,by omega,?_⟩
    intro i
    simp only [dup,if_neg (show ¬o+104+i<s+104 by omega),show o+104+i-104=o+i by omega,he]
  · exact inside_shift loc per

theorem zone_language {f : Nat → Bool} {z : Zone} (h : Valid f z) (w : Nat → Bool)
    (n : Nat) (hn : n≤z.size+104) : occurs (dup f z.s 104) w n ↔ occurs f w n := by
  obtain ⟨gap0,ls,sr,v,per,echo,loc⟩ := h
  have ab := gap0.1
  apply one_run_language (l := z.a+1) (r := z.b) (by omega) sr
  · intro i lo hi; rw [loc _ (by omega) (by omega),loc _ (by omega) (by omega),per]
  · obtain ⟨o,_,he⟩ := echo 0
    refine ⟨o+(z.a+1),?_⟩
    intro i lo hi
    rw [show o+(z.a+1)+(i-(z.a+1))=o+i by omega,he]
    apply inside_shift loc per
    · simpa [push,ls] using lo
    · simpa [push,show ¬z.b<z.s by omega,Nat.add_assoc] using hi
  · unfold Zone.size at hn; omega

end AntSharp
