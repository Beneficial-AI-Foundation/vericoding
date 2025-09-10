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
lemma OptimalDiplomasLemma(n: int, k: int)
  requires ValidInput(n, k)
  ensures OptimalDiplomas(n, k) >= 0
  ensures OptimalDiplomas(n, k) * k >= 0
  ensures OptimalDiplomas(n, k) + OptimalDiplomas(n, k) * k <= n / 2
{
}

lemma DivisionLemma(a: int, b: int)
  requires a >= 0 && b > 0
  ensures a / b >= 0
{
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
  var x := OptimalDiplomas(n, k);
  var y := x * k;
  var z := n - x - y;
  
  result := [x, y, z];
  
  assert x >= 0;
  assert y >= 0;
  assert z >= 0;
  assert |result| == 3;
  assert result[0] == x;
  assert result[1] == y;
  assert result[2] == z;
  assert result[1] == result[0] * k;
  assert result[0] + result[1] <= n / 2;
  assert result[2] == n - result[0] - result[1];
}
// </vc-code>

