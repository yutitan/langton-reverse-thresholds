import AntInverse

namespace AntGate
open TwoBlack AntInverse

def orderedSeed : List Pt := [⟨-86,-46⟩,⟨-63,-43⟩,⟨-36,0⟩,⟨-36,3⟩,⟨-35,-1⟩,
  ⟨-35,0⟩,⟨-35,1⟩,⟨-34,2⟩,⟨-34,3⟩,⟨-33,0⟩,⟨-33,3⟩,⟨-32,2⟩,⟨-31,1⟩,⟨-31,2⟩]
def direct (n : Nat) := (List.range n).map (fun i => forward[i%104]!)

set_option maxRecDepth 1000000 in
theorem ordered14 : orderedSeed.Nodup ∧ orderedSeed.length=14 ∧
    word 2453 (run 9977 (initState orderedSeed)) = direct 2453 ∧
    matchAt orderedSeed 174341 89 119 ∧ ¬matchAt orderedSeed 174341 89 120 := by
  refine ⟨by decide,rfl,?_,replay _ _ _ _ (by native_decide),?_⟩
  · have ok : fword 2453 (frun 9977 (FState.init orderedSeed))=direct 2453 := by native_decide
    simpa only [word_correct,frun_toState,FState.init_toState] using ok
  · have no : fword 120 (frun 174341 (FState.init orderedSeed))≠inverse 89 120 := by native_decide
    simpa only [matchAt,word_correct,frun_toState,FState.init_toState] using no

#print axioms ordered14
end AntGate
