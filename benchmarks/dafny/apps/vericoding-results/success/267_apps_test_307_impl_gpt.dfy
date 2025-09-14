predicate ValidInput(k2: int, k3: int, k5: int, k6: int)
{
    k2 >= 0 && k3 >= 0 && k5 >= 0 && k6 >= 0 &&
    k2 <= 5000000 && k3 <= 5000000 && k5 <= 5000000 && k6 <= 5000000
}

function OptimalSum(k2: int, k3: int, k5: int, k6: int): int
    requires ValidInput(k2, k3, k5, k6)
{
    var count256 := min(min(k2, k5), k6);
    var remaining_k2 := k2 - count256;
    var count32 := min(k3, remaining_k2);
    256 * count256 + 32 * count32
}

// <vc-helpers>
function min(a: int, b: int): int {
  if a <= b then a else b
}

lemma MinLeLeft(a: int, b: int)
  ensures min(a, b) <= a
{
  if a <= b {
    assert min(a, b) == a;
    assert min(a, b) <= a;
  } else {
    assert min(a, b) == b;
    assert b <= a;
    assert min(a, b) <= a;
  }
}

lemma MinLeRight(a: int, b: int)
  ensures min(a, b) <= b
{
  if a <= b {
    assert min(a, b) == a;
    assert a <= b;
    assert min(a, b) <= b;
  } else {
    assert min(a, b) == b;
    assert min(a, b) <= b;
  }
}

lemma MinNonNeg(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures min(a, b) >= 0
{
  if a <= b {
    assert min(a, b) == a;
    assert min(a, b) >= 0;
  } else {
    assert min(a, b) == b;
    assert min(a, b) >= 0;
  }
}

lemma OptimalSumNonNeg(k2: int, k3: int, k5: int, k6: int)
  requires ValidInput(k2, k3, k5, k6)
  ensures OptimalSum(k2, k3, k5, k6) >= 0
{
  var m1 := min(min(k2, k5), k6);
  var rem := k2 - m1;
  var m2 := min(k3, rem);

  MinNonNeg(k2, k5);
  MinNonNeg(min(k2, k5), k6);
  assert 0 <= m1;

  MinLeLeft(min(k2, k5), k6);
  assert m1 <= min(k2, k5);
  MinLeLeft(k2, k5);
  assert min(k2, k5) <= k2;
  assert m1 <= k2;
  assert rem >= 0;

  MinNonNeg(k3, rem);
  assert 0 <= m2;

  assert 0 <= 256 * m1;
  assert 0 <= 32 * m2;
  assert 0 <= 256 * m1 + 32 * m2;

  assert OptimalSum(k2, k3, k5, k6) == 256 * m1 + 32 * m2;
}
// </vc-helpers>

// <vc-spec>
method solve(k2: int, k3: int, k5: int, k6: int) returns (result: int)
    requires ValidInput(k2, k3, k5, k6)
    ensures result >= 0
    ensures result == OptimalSum(k2, k3, k5, k6)
// </vc-spec>
// <vc-code>
{
  result := OptimalSum(k2, k3, k5, k6);
  OptimalSumNonNeg(k2, k3, k5, k6);
}
// </vc-code>

