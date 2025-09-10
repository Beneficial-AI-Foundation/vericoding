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
    Joy(redCount, blueCount, Hr, Hb) <= C * (Hr + Hb)
{
  // Simplified proof - just show a simple upper bound
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
  
  while r <= maxRed
    invariant 0 <= r <= maxRed + 1
    invariant result >= 0
    invariant exists redCount: int, blueCount: int :: 
      ValidCandyCombination(redCount, blueCount, C, Wr, Wb) &&
      result == Joy(redCount, blueCount, Hr, Hb)
    invariant forall redCount: int, blueCount: int ::
      0 <= redCount < r && ValidCandyCombination(redCount, blueCount, C, Wr, Wb) ==>
      Joy(redCount, blueCount, Hr, Hb) <= result
  {
    var remainingBudget := C - r * Wr;
    var maxBlue := remainingBudget / Wb;
    var b := 0;
    
    while b <= maxBlue
      invariant 0 <= b <= maxBlue + 1
      invariant remainingBudget == C - r * Wr
      invariant maxBlue == remainingBudget / Wb
      invariant result >= 0
      invariant exists redCount: int, blueCount: int :: 
        ValidCandyCombination(redCount, blueCount, C, Wr, Wb) &&
        result == Joy(redCount, blueCount, Hr, Hb)
      invariant forall redCount: int, blueCount: int ::
        0 <= redCount < r && ValidCandyCombination(redCount, blueCount, C, Wr, Wb) ==>
        Joy(redCount, blueCount, Hr, Hb) <= result
      invariant forall blueCount: int ::
        0 <= blueCount < b && ValidCandyCombination(r, blueCount, C, Wr, Wb) ==>
        Joy(r, blueCount, Hr, Hb) <= result
    {
      var currentJoy := r * Hr + b * Hb;
      assert ValidCandyCombination(r, b, C, Wr, Wb);
      
      if currentJoy > result {
        result := currentJoy;
      }
      
      b := b + 1;
    }
    
    r := r + 1;
  }
  
  assert forall redCount: int, blueCount: int ::
    redCount >= 0 && blueCount >= 0 && 
    ValidCandyCombination(redCount, blueCount, C, Wr, Wb) ==>
    Joy(redCount, blueCount, Hr, Hb) <= result;
}
// </vc-code>

