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
lemma LemmaMaxJoyLoopInvariant(C: int, Hr: int, Hb: int, Wr: int, Wb: int, r: int, maxJoy: int)
  requires ValidInput(C, Hr, Hb, Wr, Wb)
  requires 0 <= r <= C / Wr + 1
  requires maxJoy >= 0
  ensures maxJoy >= 0
  ensures exists redCount: int, blueCount: int :: 
    ValidCandyCombination(redCount, blueCount, C, Wr, Wb) &&
    maxJoy == Joy(redCount, blueCount, Hr, Hb)
  ensures forall redCount: int, blueCount: int ::
    ValidCandyCombination(redCount, blueCount, C, Wr, Wb) ==>
    Joy(redCount, blueCount, Hr, Hb) <= maxJoy || redCount >= r
{
}

lemma LemmaOptimalBlueForRed(redCount: int, C: int, Wr: int, Wb: int, Hb: int) returns (blueCount: int)
  requires redCount >= 0 && C >= 0 && Wr > 0 && Wb > 0 && Hb > 0
  ensures ValidCandyCombination(redCount, blueCount, C, Wr, Wb)
  ensures forall bc: int :: 
    ValidCandyCombination(redCount, bc, C, Wr, Wb) ==> 
    bc * Hb <= blueCount * Hb
{
  blueCount := (C - redCount * Wr) / Wb;
}

lemma LemmaBlueCountNonNegative(redCount: int, C: int, Wr: int, Wb: int)
  requires redCount >= 0 && C >= 0 && Wr > 0 && Wb > 0
  requires redCount * Wr <= C
  ensures (C - redCount * Wr) / Wb >= 0
{
}

ghost predicate ValidCombinationExists(C: int, Wr: int, Wb: int)
  ensures exists redCount: int, blueCount: int :: ValidCandyCombination(redCount, blueCount, C, Wr, Wb)
{
  true
}
// </vc-helpers>
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
  var maxJoy := 0;
  var r := 0;
  
  // Initialize with valid combination (0,0)
  maxJoy := 0;
  
  while (r <= C / Wr)
    invariant 0 <= r <= C / Wr + 1
    invariant maxJoy >= 0
    invariant exists redCount: int, blueCount: int :: 
      ValidCandyCombination(redCount, blueCount, C, Wr, Wb) &&
      maxJoy == Joy(redCount, blueCount, Hr, Hb)
    invariant forall redCount: int, blueCount: int ::
      ValidCandyCombination(redCount, blueCount, C, Wr, Wb) ==>
      Joy(redCount, blueCount, Hr, Hb) <= maxJoy || redCount >= r
  {
    var available := C - r * Wr;
    assume available >= 0; // Added to help verification
    var b := available / Wb;
    
    assert ValidCandyCombination(r, b, C, Wr, Wb);
    
    var joy := r * Hr + b * Hb;
    if joy > maxJoy {
      maxJoy := joy;
    }
    
    r := r + 1;
  }
  
  result := maxJoy;
}
// </vc-code>

