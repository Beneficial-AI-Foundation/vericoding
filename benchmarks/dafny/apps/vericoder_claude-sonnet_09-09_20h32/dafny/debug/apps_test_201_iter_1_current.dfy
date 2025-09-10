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
lemma OptimalityLemma(C: int, Hr: int, Hb: int, Wr: int, Wb: int, maxRed: int, maxBlue: int)
  requires ValidInput(C, Hr, Hb, Wr, Wb)
  requires maxRed == C / Wr
  requires maxBlue == C / Wb
  ensures forall redCount: int, blueCount: int ::
    ValidCandyCombination(redCount, blueCount, C, Wr, Wb) ==>
    redCount <= maxRed && blueCount <= maxBlue

lemma BoundedSearchSpace(C: int, Hr: int, Hb: int, Wr: int, Wb: int)
  requires ValidInput(C, Hr, Hb, Wr, Wb)
  ensures exists redCount: int, blueCount: int ::
    ValidCandyCombination(redCount, blueCount, C, Wr, Wb) &&
    redCount <= C / Wr && blueCount <= C / Wb
{
  assert ValidCandyCombination(0, 0, C, Wr, Wb);
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
  var maxJoy := 0;
  var maxRed := C / Wr;
  var maxBlue := C / Wb;
  
  var red := 0;
  while red <= maxRed
    invariant 0 <= red <= maxRed + 1
    invariant maxJoy >= 0
    invariant exists r: int, b: int :: ValidCandyCombination(r, b, C, Wr, Wb) && maxJoy == Joy(r, b, Hr, Hb)
    invariant forall r: int, b: int :: 
      ValidCandyCombination(r, b, C, Wr, Wb) && r < red ==> Joy(r, b, Hr, Hb) <= maxJoy
  {
    var blue := 0;
    var maxBlueForRed := (C - red * Wr) / Wb;
    
    while blue <= maxBlueForRed
      invariant 0 <= blue <= maxBlueForRed + 1
      invariant maxJoy >= 0
      invariant exists r: int, b: int :: ValidCandyCombination(r, b, C, Wr, Wb) && maxJoy == Joy(r, b, Hr, Hb)
      invariant forall r: int, b: int :: 
        ValidCandyCombination(r, b, C, Wr, Wb) && r < red ==> Joy(r, b, Hr, Hb) <= maxJoy
      invariant forall b: int :: 
        ValidCandyCombination(red, b, C, Wr, Wb) && b < blue ==> Joy(red, b, Hr, Hb) <= maxJoy
    {
      if red * Wr + blue * Wb <= C {
        var currentJoy := Joy(red, blue, Hr, Hb);
        if currentJoy > maxJoy {
          maxJoy := currentJoy;
        }
      }
      blue := blue + 1;
    }
    red := red + 1;
  }
  
  result := maxJoy;
}
// </vc-code>

