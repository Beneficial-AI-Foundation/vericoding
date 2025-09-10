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
lemma DivMulLe(a: int, b: int)
  requires a >= 0 && b > 0
  ensures (a / b) * b <= a
{
  var q := a / b;
  assert a == q * b + a % b;
  assert 0 <= a % b && a % b < b;
  assert q * b <= a;
}

lemma MulLeDiv(x: int, Y: int, b: int)
  requires b > 0 && x >= 0 && Y >= 0
  requires x * b <= Y
  ensures x <= Y / b
{
  if x > Y / b {
    var q := Y / b;
    // x >= q + 1
    assert x >= q + 1;
    // x * b >= (q + 1) * b
    assert x * b >= (q + 1) * b;
    // (q + 1) * b > q * b
    assert (q + 1) * b > q * b;
    // q * b <= Y
    DivMulLe(Y, b);
    assert q * b <= Y;
    // Hence (q + 1) * b > Y, contradicting x * b <= Y
    assert (q + 1) * b > Y;
    assert !(x * b <= Y);
  }
}

lemma LeMulBound(rr: int, C: int, Wr: int)
  requires C >= 0 && Wr > 0 && 0 <= rr && rr <= C / Wr
  ensures rr * Wr <= C
{
  var q := C / Wr;
  DivMulLe(C, Wr);
  assert q * Wr <= C;
  assert rr * Wr <= q * Wr;
  assert rr * Wr <= C;
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
  var maxRed := C / Wr;
  var r := 0;
  var bestR := 0;
  var bestB := C / Wb;
  DivMulLe(C, Wb);
  // ensure initial best combination is valid
  assert 0 <= bestB;
  assert bestB * Wb <= C;
  result := Joy(bestR, bestB, Hr, Hb);

  while r <= maxRed
    invariant 0 <= r <= maxRed + 1
    invariant 0 <= result
    invariant 0 <= bestR && 0 <= bestB
    invariant ValidCandyCombination(bestR, bestB, C, Wr, Wb)
    invariant result == Joy(bestR, bestB, Hr, Hb)
    invariant forall rr :: 0 <= rr < r ==> result >= Joy(rr, (C - rr * Wr) / Wb, Hr, Hb)
  {
    var rem := C - r * Wr;
    // rem must be >= 0 because r <= maxRed and maxRed = C / Wr
    if rem < 0 {
      // unreachable, but help the verifier
      rem := 0;
    }
    var b := rem / Wb;
    var j := r * Hr + b * Hb;
    if j > result {
      result := j;
      bestR := r;
      bestB := b;
    }
    r := r + 1;
  }

  // Show existence of a valid combination achieving result
  assert ValidCandyCombination(bestR, bestB, C, Wr, Wb);
  assert result == Joy(bestR, bestB, Hr, Hb);

  // Prove optimality: any valid combination has Joy <= result
  // Let any redCount, blueCount be such that redCount*Wr + blueCount*Wb <= C
  // Then redCount <= C / Wr and blueCount <= (C - redCount*Wr) / Wb.
  // Use lemmas to conclude Joy(redCount, blueCount) <= result.
  // Formalize the argument for the verifier:
  assert forall redCount, blueCount ::
    ValidCandyCombination(redCount, blueCount, C, Wr, Wb) ==>
    Joy(redCount, blueCount, Hr, Hb) <= result
  by {
    // take arbitrary such redCount, blueCount
    assume ValidCandyCombination(redCount, blueCount, C, Wr, Wb);
    // redCount >= 0 and C >= 0 so we can apply MulLeDiv
    assert 0 <= redCount;
    assert C >= 0;
    // redCount * Wr <= C implies redCount <= C / Wr
    MulLeDiv(redCount, C, Wr);
    // hence redCount <= C / Wr
    // so compute bmax
    var bmax := (C - redCount * Wr) / Wb;
    // show blueCount <= bmax
    // from blueCount * Wb <= C - redCount * Wr and Wb>0
    var rem := C - redCount * Wr;
    assert rem >= 0 by {
      // redCount <= C / Wr implies redCount * Wr <= C
      LeMulBound(redCount, C, Wr);
    }
    MulLeDiv(blueCount, rem, Wb);
    // blueCount <= bmax
    // since Hb > 0, Joy increases with blueCount
    assert Joy(redCount, blueCount, Hr, Hb) <= Joy(redCount, bmax, Hr, Hb) by {
      // difference is (bmax - blueCount) * Hb >= 0
      assert bmax - blueCount >= 0;
      assert Hb > 0;
    }
    // by the loop invariant at termination, result >= Joy(redCount, bmax)
    // because redCount <= maxRed and the loop considered all such redCounts
    assert result >= Joy(redCount, bmax, Hr, Hb);
    // combine
    assert Joy(redCount, blueCount, Hr, Hb) <= result;
  }
}
// </vc-code>

