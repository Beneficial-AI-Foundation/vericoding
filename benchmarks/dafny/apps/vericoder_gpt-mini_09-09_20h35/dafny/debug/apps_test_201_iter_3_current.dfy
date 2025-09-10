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
// Added no helpers; existing predicates and functions are sufficient.
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
  var maxR := C / Wr;
  var maxB := C / Wb;
  var bestR := 0;
  var bestB := 0;
  var res := 0;
  var r := 0;
  // Initially bestR=0,bestB=0 is a valid combination (0 cost), res = Joy(0,0)=0
  while r <= maxR
    invariant 0 <= r <= maxR + 1
    invariant 0 <= bestR <= maxR
    invariant 0 <= bestB <= maxB
    invariant res == Joy(bestR, bestB, Hr, Hb)
    invariant ValidCandyCombination(bestR, bestB, C, Wr, Wb)
    invariant forall rr, bb :: 0 <= rr < r && 0 <= bb <= maxB && rr * Wr + bb * Wb <= C ==> res >= Joy(rr, bb, Hr, Hb)
  {
    var b := 0;
    while b <= maxB
      invariant 0 <= b <= maxB + 1
      invariant 0 <= bestR <= maxR
      invariant 0 <= bestB <= maxB
      invariant res == Joy(bestR, bestB, Hr, Hb)
      invariant ValidCandyCombination(bestR, bestB, C, Wr, Wb)
      invariant forall rr, bb :: 0 <= rr < r && 0 <= bb <= maxB && rr * Wr + bb * Wb <= C ==> res >= Joy(rr, bb, Hr, Hb)
      invariant forall bb0 :: 0 <= bb0 < b && r * Wr + bb0 * Wb <= C ==> res >= Joy(r, bb0, Hr, Hb)
    {
      if r * Wr + b * Wb <= C {
        var j := r * Hr + b * Hb;
        if j > res {
          res := j;
          bestR := r;
          bestB := b;
        }
      }
      b := b + 1;
    }
    r := r + 1;
  }
  result := res;
}
// </vc-code>

