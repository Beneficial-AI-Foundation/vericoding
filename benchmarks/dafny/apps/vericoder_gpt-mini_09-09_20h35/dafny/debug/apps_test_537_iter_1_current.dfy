predicate ValidInput(n: int, k: int) {
    n >= 0 && k >= 0 && k + 1 > 0
}

predicate ValidOutput(result: seq<int>, n: int, k: int) {
    |result| == 3 &&
    result[0] >= 0 && result[1] >= 0 && result[2] >= 0 &&
    result[1] == result[0] * k &&
    result[0] + result[1] <= n / 2 &&
    result[2] == n - result[0] - result[1]
}

function OptimalDiplomas(n: int, k: int): int
    requires ValidInput(n, k)
{
    (n / 2) / (k + 1)
}

// <vc-helpers>
lemma DivNonneg(a: int, b: int)
    requires a >= 0 && b > 0
    ensures a / b >= 0
{
    var q := a / b;
    assert q >= 0;
}

lemma DivMulLeNonneg(a: int, b: int)
    requires a >= 0 && b > 0
    ensures (a / b) * b <= a
{
    var q := a / b;
    assert q * b <= a;
}

lemma DivLeSelf(a: int, b: int)
    requires a >= 0 && b > 0
    ensures a / b <= a
{
    var q := a / b;
    assert q <= a;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: seq<int>)
    requires ValidInput(n, k)
    ensures ValidOutput(result, n, k)
    ensures result[0] == OptimalDiplomas(n, k)
// </vc-spec>
// <vc-code>
{
  var x := (n / 2) / (k + 1);
  var y := x * k;
  var z := n - x - y;

  DivNonneg(n / 2, k + 1);
  DivMulLeNonneg(n / 2, k + 1);
  DivLeSelf(n, 2);

  assert x >= 0;
  assert y >= 0;
  assert x * (k + 1) == x + y;
  assert x + y <= n / 2;
  assert n - (x + y) >= 0;

  result := [x, y, z];
  return;
}
// </vc-code>

