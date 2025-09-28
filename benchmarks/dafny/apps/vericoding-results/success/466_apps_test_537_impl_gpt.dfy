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
lemma DivMulLe(x: int, d: int)
  requires d > 0
  ensures (x / d) * d <= x
{
  assert x == (x / d) * d + x % d;
  assert 0 <= x % d;
  assert (x / d) * d <= (x / d) * d + x % d;
  assert (x / d) * d <= x;
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
  var a := OptimalDiplomas(n, k);
  var b := a * k;
  var c := n - a - b;
  var t := n / 2;

  assert k + 1 > 0;
  assert a == t / (k + 1);
  DivMulLe(t, k + 1);
  assert a * (k + 1) <= t;
  assert a + b == a * (k + 1);
  assert a + b <= n / 2;

  assert t >= 0;
  assert a >= 0;
  assert b >= 0;

  assert n - (a + b) >= n - n / 2;
  assert n - n / 2 >= 0;
  assert c == n - (a + b);
  assert c >= 0;

  result := [a, b, c];
}
// </vc-code>

