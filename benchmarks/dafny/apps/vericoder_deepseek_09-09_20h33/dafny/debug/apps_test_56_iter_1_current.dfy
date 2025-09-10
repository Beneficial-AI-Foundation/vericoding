predicate ValidInput(n: int, t: int) {
  1 <= n <= 10 && 0 <= t <= 10000
}

function TotalGlasses(n: int): int {
  n * (n + 1) / 2
}

predicate ValidResult(result: int, n: int, t: int) {
  result >= 0 && result <= TotalGlasses(n)
}

predicate CorrectForEdgeCases(result: int, n: int, t: int) {
  (t == 0 ==> result == 0) &&
  (n == 1 && t >= 1 ==> result == 1) &&
  (n == 1 && t == 0 ==> result == 0) &&
  (t >= 1 && n > 1 ==> result >= 1)
}

// <vc-helpers>
lemma GeometricSum(n: int)
  requires 1 <= n <= 10
  ensures TotalGlasses(n) == n * (n + 1) / 2
{
}

lemma TotalGlassesBounds(n: int)
  requires 1 <= n <= 10
  ensures 0 <= TotalGlasses(n) <= 55
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, t: int) returns (result: int)
  requires ValidInput(n, t)
  ensures ValidResult(result, n, t)
  ensures CorrectForEdgeCases(result, n, t)
// </vc-spec>
// <vc-code>
{
  result := 0;
  var i := 1;
  while i <= n && t >= i
    invariant 0 <= i <= n + 1
    invariant result == if i > 0 then i - 1 else 0
    decreases n - i
  {
    result := result + 1;
    t := t - i;
    i := i + 1;
  }
}
// </vc-code>

