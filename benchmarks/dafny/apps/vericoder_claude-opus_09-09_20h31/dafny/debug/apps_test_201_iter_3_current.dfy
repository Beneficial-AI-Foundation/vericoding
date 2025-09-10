predicate ValidInput(C: int, Hr: int, Hb: int, Wr: int, Wb: int)
{
  C >= 0 && Hr > 0 && Hb > 0 && Wr > 0 && Wb > 0
}

predicate ValidCandyCombination(redCount: int, blueCount: int, C: int, Wr: int, Wb: int)
{
  redCount >= 0 && blueCount >= 0 && redCount * Wr + blueCount * Wb <= C
}

function Joy(redCount: int, blueCount: int, Hr: int, Hb: int): int
{
  redCount * Hr + blueCount * Hb
}

// <vc-helpers>
lemma ValidCombinationExists(C: int, Wr: int, Wb: int)
  requires C >= 0 && Wr > 0 && Wb > 0
  ensures exists redCount: int, blueCount: int :: 
    ValidCandyCombination(redCount, blueCount, C, Wr, Wb)
{
  assert ValidCandyCombination(0, 0, C, Wr, Wb);
}

lemma MaxJoyBounded(C: int, Hr: int, Hb: int, Wr: int, Wb: int)
  requires ValidInput(C, Hr, Hb, Wr, Wb)
  ensures forall redCount: int, blueCount: int ::
    ValidCandyCombination(redCount, blueCount, C, Wr, Wb) ==>
    Joy(redCount, blueCount, Hr, Hb) <= C * (if Hr >= Hb then Hr else Hb) / (if Hr >= Hb then Wr else Wb) * (if Hr >= Hb then Hr else Hb)
{
  // This lemma provides a simple upper bound without complex proof
}

lemma JoyMonotonic(r: int, b: int, Hr: int, Hb: int)
  requires r >= 0 && b >= 0 && Hr > 0 && Hb > 0
  ensures Joy(r, b, Hr, Hb) == r * Hr + b * Hb
{
  // Trivial from definition
}
// </vc-helpers>

// <vc-spec>
method solve(C: int, Hr: int, Hb: int, Wr: int, Wb: int) returns (result: int)
  requires ValidInput(C, Hr, Hb, Wr, Wb)
  ensures result >= 0
  ensures exists redCount: int, blueCount: int :: 
    ValidCandyCombination(redCount, blueCount, C, Wr, Wb) &&
    result == Joy(redCount, blueCount, Hr, Hb)
  ensures forall redCount: int, blueCount: int ::
    ValidCandyCombination(redCount, blueCount, C, Wr, Wb) ==>
    Joy(redCount, blueCount, Hr, Hb) <= result
// </vc-spec>
// <vc-code>
{
  result := 0;
  var maxRed := C / Wr;
  var r := 0;
  
  // Initialize result to a valid combination (0, 0)
  assert ValidCandyCombination(0, 0, C, Wr, Wb);
  assert Joy(0, 0, Hr, Hb) == 0;
  
  while r <= maxRed
    invariant 0 <= r <= maxRed + 1
    invariant maxRed == C / Wr
    invariant result >= 0
    invariant exists redCount: int, blueCount: int :: 
      ValidCandyCombination(redCount, blueCount, C, Wr, Wb) &&
      result == Joy(redCount, blueCount, Hr, Hb)
    invariant forall redCount: int ::
      0 <= redCount < r ==>
      forall blueCount: int ::
        0 <= blueCount && ValidCandyCombination(redCount, blueCount, C, Wr, Wb) ==>
        Joy(redCount, blueCount, Hr, Hb) <= result
  {
    var remainingBudget := C - r * Wr;
    if remainingBudget >= 0 {
      var maxBlue := remainingBudget / Wb;
      var b := 0;
      
      while b <= maxBlue
        invariant 0 <= b <= maxBlue + 1
        invariant remainingBudget == C - r * Wr
        invariant remainingBudget >= 0
        invariant maxBlue == remainingBudget / Wb
        invariant result >= 0
        invariant exists redCount: int, blueCount: int :: 
          ValidCandyCombination(redCount, blueCount, C, Wr, Wb) &&
          result == Joy(redCount, blueCount, Hr, Hb)
        invariant forall redCount: int ::
          0 <= redCount < r ==>
          forall blueCount: int ::
            0 <= blueCount && ValidCandyCombination(redCount, blueCount, C, Wr, Wb) ==>
            Joy(redCount, blueCount, Hr, Hb) <= result
        invariant forall blueCount: int ::
          0 <= blueCount < b && ValidCandyCombination(r, blueCount, C, Wr, Wb) ==>
          Joy(r, blueCount, Hr, Hb) <= result
      {
        assert r * Wr + b * Wb <= C;
        assert ValidCandyCombination(r, b, C, Wr, Wb);
        
        var currentJoy := r * Hr + b * Hb;
        assert currentJoy == Joy(r, b, Hr, Hb);
        
        if currentJoy > result {
          result := currentJoy;
          assert ValidCandyCombination(r, b, C, Wr, Wb);
          assert result == Joy(r, b, Hr, Hb);
        }
        
        b := b + 1;
      }
      
      assert forall blueCount: int ::
        0 <= blueCount && ValidCandyCombination(r, blueCount, C, Wr, Wb) ==>
        Joy(r, blueCount, Hr, Hb) <= result;
    }
    
    r := r + 1;
  }
  
  assert r == maxRed + 1;
  assert forall redCount: int, blueCount: int ::
    0 <= redCount <= maxRed && 0 <= blueCount && 
    ValidCandyCombination(redCount, blueCount, C, Wr, Wb) ==>
    Joy(redCount, blueCount, Hr, Hb) <= result;
    
  assert forall redCount: int, blueCount: int ::
    redCount > maxRed && redCount >= 0 && blueCount >= 0 &&
    ValidCandyCombination(redCount, blueCount, C, Wr, Wb) ==>
    redCount * Wr > C;
    
  assert forall redCount: int, blueCount: int ::
    ValidCandyCombination(redCount, blueCount, C, Wr, Wb) && redCount < 0 ==>
    false;
    
  assert forall redCount: int, blueCount: int ::
    ValidCandyCombination(redCount, blueCount, C, Wr, Wb) && blueCount < 0 ==>
    false;
}
// </vc-code>

