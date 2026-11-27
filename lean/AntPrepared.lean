/- Retains the consecutive-member relation certified by TwoBlack.Check.
   Adapted from fam1_core/check1_sound, upstream 95e896e3035e992e48ce9d28a5ded8568c86e835. -/
import TwoBlack.Level1
namespace AntPlane
open TwoBlack
theorem prepared_core (F : Fam1) (cd : CorridorData) (hδ : cd.δ = F.δ) (n s : Nat) (u : Pt) (A : Int)
    (hDC : cd.D + 40 < cd.C)
    (gap : ∀ j, 1 ≤ j → j < cd.J → cd.m j + 104 < cd.m (j + 1))
    (hfar : ∀ b ∈ F.far, F.δ.phi (b + Pt.smul (n : Int) F.δ.v) ≥ cd.C - 4)
    (hnear : ∀ b ∈ F.near, F.δ.phi b < cd.C - 16)
    (hsJ : cd.start cd.J ≤ s)
    (hsign : (cd.J % 2 = 0 → F.δ.phi u ≤ 0) ∧ (cd.J % 2 = 1 → F.δ.phi u ≥ 0))
    (hsw : ∀ j, 1 ≤ j → j ≤ cd.J →
      (run (cd.m j + 104) (initState (F.cells n))).pos = (run (cd.m j) (initState (F.cells n))).pos + cd.sv j ∧
      (run (cd.m j + 104) (initState (F.cells n))).dir = (run (cd.m j) (initState (F.cells n))).dir ∧
      ∀ w, cd.D + 8 < cd.δ.phi w → cd.δ.phi w < cd.C - 8 →
        (run (cd.m j + 104) (initState (F.cells n))).black w =
          (run (cd.m j) (initState (F.cells n))).black (w - cd.sv j))
    (hc4 : ∀ q, q ≤ cd.J → ∀ t, t < s + 104 → cd.InInt q t →
      (q % 2 = 0 → cd.δ.phi (run t (initState (F.cells n))).pos < cd.C - 16) ∧
      (q % 2 = 1 → cd.δ.phi (run t (initState (F.cells n))).pos > cd.D + 16))
    (hu : StdDrift u)
    (hag : Agree (fun z => dot u z > A) u (run s (initState (F.cells n))) (run (s + 104) (initState (F.cells n))))
    (hin : ∀ j, j < 104 → dot u (run (s + j) (initState (F.cells n))).pos > A) :
    ∀ k, CorridorHyp (cd.iter k) (initState (F.cells (n + k))) (initState (F.cells (n + (k+1)))) := by
  let X : Nat → State := fun k => initState (F.cells (n + k))
  have per := halfplane_obs (initState (F.cells n)) (fun z => dot u z > A) u s 104 (by decide)
    (fun z hz => stdDrift_dot_pos hu z A hz) hag hin
  have c4 : ∀ q, q ≤ cd.J → ∀ t, cd.InInt q t →
      (q % 2 = 0 → cd.δ.phi (run t (initState (F.cells n))).pos < cd.C - 16) ∧
      (q % 2 = 1 → cd.δ.phi (run t (initState (F.cells n))).pos > cd.D + 16) := by
    intro q hq t hI
    by_cases ht : t < s + 104
    · exact hc4 q hq t ht hI
    · have hqJ : q = cd.J := by
        rcases Nat.lt_or_ge q cd.J with hlt | hge
        · exfalso
          have h2 := hI.2 hlt
          have hmono := m_mono cd gap (q + 1) cd.J (by omega) (by omega) (Nat.le_refl _)
          have hsJ' : cd.m cd.J ≤ s := by
            have := hsJ; unfold CorridorData.start at this; split at this
            · omega
            · exact this
          omega
        · omega
      subst hqJ
      obtain ⟨c, j, hj, rfl⟩ : ∃ c j, j < 104 ∧ t = s + c * 104 + j :=
        ⟨(t - s) / 104, (t - s) % 104, Nat.mod_lt _ (by decide), by omega⟩
      have hp : (run (s + c * 104 + j) (initState (F.cells n))).pos =
          (run (s + j) (initState (F.cells n))).pos + Pt.smul (c : Int) u := by
        have := congrArg Obs.pos (per c j)
        simpa [observe, Obs.shift] using this
      have hI' : cd.InInt cd.J (s + j) := ⟨by omega, fun h => absurd h (Nat.lt_irrefl _)⟩
      have base := hc4 cd.J (Nat.le_refl _) (s + j) (by omega) hI'
      rw [hp, Diag.phi_add, Diag.phi_smul]
      rw [hδ] at base ⊢
      constructor
      · intro hpar
        have hb := base.1 hpar
        have hs := hsign.1 hpar
        rcases phi_std F.δ hu with e | e | e <;> rw [e] at hs ⊢ <;> omega
      · intro hpar
        have hb := base.2 hpar
        have hs := hsign.2 hpar
        rcases phi_std F.δ hu with e | e | e <;> rw [e] at hs ⊢ <;> omega
  have hinit := fam_init F n cd.C hfar hnear
  have H0 : CorridorHyp cd (X 0) (X 1) := by
    refine ⟨hDC, gap, fun j h1 h2 => (hsw j h1 h2).1, fun j h1 h2 => (hsw j h1 h2).2.1,
      fun j h1 h2 => (hsw j h1 h2).2.2, c4, ?_⟩
    have := hinit 0
    simp only [Nat.add_zero, Int.natCast_zero, Int.mul_zero, Int.add_zero] at this
    rw [hδ]
    exact this
  intro k
  induction k with
  | zero => exact H0
  | succ k ih =>
    apply corridor_succ (cd.iter k) (X k) (X (k+1)) (X (k+2)) ih
    rw [CorridorData.iter_δ, CorridorData.iter_C, hδ]
    have hi := hinit (k+1)
    push_cast at hi ⊢
    simpa only [Int.mul_add, Int.mul_one, Int.add_assoc,
      Nat.add_assoc] using hi

theorem prepared_of_check (F : Fam1) (H : Hint1) (hc : check1 F H = true) :
    ∀ k, CorridorHyp ((H.cd F).iter k) (initState (F.cells (H.n + k))) (initState (F.cells (H.n + (k+1)))) := by
  simp only [check1, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hDC, hgap⟩, hfar⟩, hnear⟩, hsJ⟩, hsign⟩, hsw⟩, hc4⟩, hstd⟩, hcpos⟩, hcdir⟩, hcag⟩,
    hreads⟩ := hc
  have runX : ∀ t, run t (initState (F.cells H.n)) = (frun t (FState.init (F.cells H.n))).toState := by
    intro t; rw [frun_toState, FState.init_toState]
  apply prepared_core F (H.cd F) rfl H.n H.s H.u H.A hDC
  · intro j hj1 hj2
    have := hgap j (List.mem_range.mpr hj2)
    simp at this
    rcases this with h | h
    · omega
    · exact h
  · exact hfar
  · exact hnear
  · exact hsJ
  · constructor
    · intro he; simp [he] at hsign; exact hsign
    · intro he; have : ¬ ((H.cd F).J % 2 = 0) := by omega
      simp [this] at hsign; exact hsign
  · intro j hj1 hj2
    have h := hsw (j - 1) (List.mem_range.mpr (by omega))
    rw [show j - 1 + 1 = j by omega] at h
    simp only [switchB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hp, hd⟩, ha⟩ := h
    rw [runX, runX, frun_add, FState.toState_pos, FState.toState_pos, FState.toState_dir, FState.toState_dir]
    refine ⟨hp, hd, ?_⟩
    intro w hw1 hw2
    rw [FState.toState_black, FState.toState_black]
    have := agreeB_sound ha (w - (H.cd F).sv j) (by simp [Pt.sub_add_cancel]; exact ⟨hw1, hw2⟩)
    rw [Pt.sub_add_cancel] at this
    exact this
  · intro q hq t ht hI
    have h1 := c4loopB_sound hc4 t ht
    simp only [Nat.zero_add, c4okB, List.all_eq_true, List.mem_range] at h1
    have h2 := h1 q (by omega)
    have hib : inIntB (H.cd F) q t = true := by
      simp only [inIntB, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not]
      refine ⟨hI.1, ?_⟩
      by_cases hqJ : q < (H.cd F).J
      · exact Or.inr (hI.2 hqJ)
      · exact Or.inl hqJ
    simp only [hib, Bool.not_true, Bool.false_or, boundB] at h2
    rw [runX]
    constructor
    · intro he; simp [he] at h2; exact h2
    · intro he; have : ¬ (q % 2 = 0) := by omega
      simp [this] at h2; exact h2
  · exact stdDriftB_sound hstd
  · rw [runX, runX, frun_add]
    refine ⟨?_, ?_, ?_⟩
    · rw [FState.toState_pos, FState.toState_pos]; exact hcpos
    · rw [FState.toState_dir, FState.toState_dir]; exact hcdir
    · intro z hz
      rw [FState.toState_black, FState.toState_black]
      exact agreeB_sound hcag z (by simp at hz ⊢; exact hz)
  · intro j hj
    rw [runX, frun_add]
    have := readsB_sound hreads j hj
    simp at this
    exact this


end AntPlane

