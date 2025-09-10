predicate ValidInput(k: int, a: int, b: int)
{
  k > 0 && a <= b
}

function FloorDiv(a: int, b: int): int
  requires b > 0
{
  if a >= 0 then a / b
  else (a - b + 1) / b
}

function CountDivisiblesInRange(k: int, a: int, b: int): int
  requires k > 0
  requires a <= b
{
  FloorDiv(b, k) - FloorDiv(a - 1, k)
}

// <vc-helpers>
lemma FloorDivLemma(a: int, b: int)
  requires b > 0
  ensures FloorDiv(a, b) * b <= a < (FloorDiv(a, b) + 1) * b
{
  if a >= 0 {
    assert a / b * b <= a < (a / b + 1) * b;
  } else {
    var q := (a - b + 1) / b;
    assert q * b <= a < (q + 1) * b;
    // Additional assertions to prove the bounds
    assert (a - b + 1) <= q * b + (b - 1);  // Since q = (a - b + 1)/b, so q*b <= a - b + 1 <= q*b + (b-1)
    assert a < q * b + b;
  }
}

lemma CountDivisiblesInRangeLemma(k: int, a: int, b: int, x: int)
  requires k > 0 && a <= b
  requires a <= x <= b
  requires k * (FloorDiv(a - 1, k) + 1) <= x <= k * FloorDiv(b, k)
  ensures x % k == 0
{
  FloorDivLemma(x, k);
  var qx := FloorDiv(x, k);
  assert qx * k <= x < (qx + 1) * k;
  
  // The key insight: since x >= k * (FloorDiv(a - 1, k) + 1) and k * (FloorDiv(a - 1, k) + 1) is divisible by k
  // and x <= k * FloorDiv(b, k) which is also divisible by k, x must be divisible by k
  
  // Prove that qx >= FloorDiv(a - 1, k) + 1
  var qa := FloorDiv(a - 1, k);
  FloorDivLemma(a - 1, k);
  assert (qa + 1) * k > a - 1;  // From FloorDivLemma: a - 1 < (qa + 1) * k
  
  // Since x >= k * (qa + 1), we have qx >= qa + 1
  // And since x <= k * FloorDiv(b, k), we have qx <= FloorDiv(b, k)
  
  // The key point: x is exactly qx * k, not just in the range [qx*k, (qx+1)*k)
  // This is because the lower bound k*(qa+1) is a multiple of k, and x is at least that
  assert x >= (qa + 1) * k;
  assert qx >= qa + 1;
  assert x >= qx * k;
  
  // Since x < (qx + 1) * k and x is an integer, x - qx * k < k
  // But we also know x ≥ qx * k, so 0 ≤ x - qx * k < k
  // And since x ≥ (qa + 1) * k and qx ≥ qa + 1, x must be exactly divisible by k
  assert x == qx * k + (x % k);
  assert x % k < k;
  assert x % k >= 0;
}

lemma FloorDivRangeLemma(a: int, b: int, k: int)
  requires k > 0
  requires a <= b
  ensures FloorDiv(a - 1, k) <= FloorDiv(b, k)
{
  FloorDivLemma(a - 1, k);
  FloorDivLemma(b, k);
  
  // Since a <= b, we have a - 1 <= b
  // FloorDiv is a non-decreasing function for fixed k > 0
  // So FloorDiv(a - 1, k) <= FloorDiv(b, k)
  
  // Prove by considering the definition of FloorDiv
  if a - 1 >= 0 {
    assert (a - 1) / k <= b / k;
  } else if b >= 0 {
    // a-1 < 0, b >= 0
    assert (a - b + 1) / k <= b / k;
  } else {
    // Both a-1 and b are negative
    assert (a - b + 1) / k <= (b - b + 1) / k;  // Since a <= b, a-b+1 <= 1
    assert (b - b + 1) / k == 1 / k == 0;        // Since k > 1, 1/k = 0
  }
}
// </vc-helpers>

// <vc-spec>
method solve(k: int, a: int, b: int) returns (result: int)
  requires ValidInput(k, a, b)
  ensures result >= 0
  ensures result == CountDivisiblesInRange(k, a, b)
// </vc-spec>
// <vc-code>
{
  result := FloorDiv(b, k) - FloorDiv(a - 1, k);
  
  // Use the lemmas to prove non-negativity
  var qb := FloorDiv(b, k);
  var qa := FloorDiv(a - 1, k);
  FloorDivRangeLemma(a, b, k);
  assert qa <= qb;
  assert result >= 0;
}
// </vc-code>

