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
// Added no additional helper lemmas; using a single-index enumeration of pairs to simplify verification.
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
  var total := (maxR + 1) * (maxB + 1);
  var bestR := 0;
  var bestB := 0;
  var res := 0;
  var k := 0;
  // Initially bestR=0,bestB=0 is a valid combination (0 cost), res = Joy(0,0)=0
  while k < total
    decreases total - k
    invariant 0 <= k <= total
    invariant 0 <= bestR <= maxR
    invariant 0 <= bestB <= maxB
    invariant res == Joy(bestR, bestB, Hr, Hb)
    invariant ValidCandyCombination(bestR, bestB, C, Wr, Wb)
    invariant forall kk :: 0 <= kk < k && ValidCandyCombination(kk / (maxB + 1), kk % (maxB + 1), C, Wr, Wb) ==> res >= Joy(kk / (maxB + 1), kk % (maxB + 1), Hr, Hb)
  {
    var r := k / (maxB + 1);
    var b := k % (maxB + 1);
    if r * Wr + b * Wb <= C {
      var j := r * Hr + b * Hb;
      if j > res {
        res := j;
        bestR := r;
        bestB := b;
      }
    }
    k := k + 1;
  }
  result := res;
}
// </vc-code>

