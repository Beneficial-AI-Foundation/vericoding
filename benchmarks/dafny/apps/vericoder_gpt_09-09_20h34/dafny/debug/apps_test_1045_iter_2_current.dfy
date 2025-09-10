predicate ValidInput(n: int) {
    n >= 1
}

function CubesForLevel(level: int): int
    requires level >= 1
{
    level * (level + 1) / 2
}

function TotalCubesForHeight(h: int): int
    requires h >= 1
{
    h * (h + 1) * (h + 2) / 6
}

predicate ValidPyramidHeight(n: int, h: int) {
    ValidInput(n) && h >= 1 && 
    TotalCubesForHeight(h) <= n &&
    TotalCubesForHeight(h + 1) > n
}

// <vc-helpers>
lemma T_lower_bound(k: int)
    requires k >= 1
    ensures TotalCubesForHeight(k) >= k
{
    // (k+1) >= 2 and (k+2) >= 3
    assert k + 1 >= 2;
    assert k + 2 >= 3;

    // Hence (k+1)*(k+2) >= 2*3 == 6
    assert (k + 1) * (k + 2) >= 2 * 3;
    assert (k + 1) * (k + 2) >= 6;

    // Multiply both sides by k (which is >= 1 >= 0)
    assert k * ((k + 1) * (k + 2)) >= k * 6;

    // Divide both sides by 6 (monotonic for positive divisor)
    assert (k * (k + 1) * (k + 2)) / 6 >= (k * 6) / 6;

    assert (k * 6) / 6 == k;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result >= 1
    ensures ValidPyramidHeight(n, result)
// </vc-spec>
// <vc-code>
{
  var h := 1;

  // Establish loop invariants initially
  assert h >= 1;
  assert TotalCubesForHeight(1) == 1;
  assert TotalCubesForHeight(h) <= n; // since n >= 1 by precondition
  assert h <= n; // since h == 1 and n >= 1

  while TotalCubesForHeight(h + 1) <= n
    invariant h >= 1
    invariant h <= n
    invariant TotalCubesForHeight(h) <= n
    decreases n - h
  {
    // From the guard and lower bound, infer h + 1 <= n to keep decreases non-negative
    T_lower_bound(h + 1);
    assert h + 1 <= n;

    h := h + 1;
  }
  result := h;
}
// </vc-code>

