import AntRays

namespace AntPlane
open TwoBlack AntInverse

/- The two adjacent letters streams have origins t and t+104. The zip
ends at t=s-1, since the permanently periodic tail starts at s. -/
def allMarks (f : FState) (s : Nat) : List Nat :=
  let w := fword (s+104) f
  ((w.zip (w.drop 104)).zipIdx).filterMap fun ((x,y),i) => if x==y then none else some i

def isStandard (f : FState) : Bool :=
  let w := fword 104 f
  let twice := forward ++ forward
  (List.range 104).any fun i => (twice.drop i).take 104 == w

def gapStats (p : Fam1 × Hint1) : Bool × Nat × Nat :=
  let f := FState.init (p.1.cells p.2.n)
  let cuts := p.2.ms
  let marks := allMarks f p.2.s
  let pairs := marks.zip (marks.drop 1)
  let inside := fun (ab : Nat × Nat) (j : Nat) => decide (ab.1<j ∧ j≤ab.2)
  let active := pairs.filter fun ab => cuts.any (inside ab)
  let others := pairs.filter fun ab => !(cuts.any (inside ab))
  let gaps := active.map (fun ab => ab.2-ab.1)
  let shortest := gaps.foldl min p.2.s
  let largestOther := others.foldl (fun a ab => max a (ab.2-ab.1)) 0
  let clean := (active.length == cuts.length) && cuts.all (fun j =>
      active.any (fun ab => inside ab j) && isStandard (frun j f)) &&
    active.all (fun ab => decide (ab.2+104 < p.2.s)) &&
    (active.zip (active.drop 1)).all (fun (ab,bc) => decide (ab.2+104 < bc.1+1)) &&
    certAt (frun p.2.s f) && isStandard (frun p.2.s f)
  (clean,shortest+104,largestOther)

def cutTable : List (Nat × Nat) := [(5006,20),(5007,20),(5008,24),(5020,71),(5021,21),
  (5022,24),(5025,20),(5031,46),(5038,21),(5039,20),(5040,20),(5048,27),(5049,34),
  (5050,20),(5053,20),(5054,41),(5055,34),(5063,29),(5064,34),(4978,47),(5068,20),(5082,20)]

set_option maxRecDepth 1000000 in
theorem gap_table_checked : level1Families.map gapStats = cutTable.map (fun row => (true,row)) := by
  native_decide

#print axioms gap_table_checked
end AntPlane
