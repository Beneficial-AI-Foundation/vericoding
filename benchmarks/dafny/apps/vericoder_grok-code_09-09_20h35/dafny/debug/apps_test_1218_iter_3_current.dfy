predicate ValidInput(n: int, k: int) {
    n >= 1 && k >= 2
}

function ImpossibilityCondition(n: int, k: int): bool
    requires ValidInput(n, k)
{
    2 * (n - 1) - k * (k - 1) > 0
}

predicate ValidSolution(n: int, k: int, result: int)
    requires ValidInput(n, k)
{
    if ImpossibilityCondition(n, k) then
        result == -1
    else
        result >= 0 && result <= k &&
        exists x: int :: 
            x >= 0 && 
            x * x - x + (2 * (n - 1) - k * (k - 1)) <= 0 && 
            (x == 0 || (x + 1) * (x + 1) - (x + 1) + (2 * (n - 1) - k * (k - 1)) > 0) &&
            result == k - x
}

// <vc-helpers>
lemma ValidSolutionForK(n: int, k: int)
  requires ValidInput(n, k)
  requires !ImpossibilityCondition(n, k)
  ensures ValidSolution(n, k, k)
{
  var c := 2 * (n - 1) - k * (k - 1);
  assert c <= 0;
  assert 0 >= 0;
  assert 0 <= 0 && (0 == 0 || (1 * 1 - 1 + c) > 0);
  assert k - 0 == k;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires ValidInput(n, k)
    ensures result >= -1
    ensures (result == -1) <==> ImpossibilityCondition(n, k)
    ensures ValidSolution(n, k, result)
// </vc-spec>
// <vc-code>
{
  var c := 2 * (n - 1) - k * (k - 1);
  if c > 0 {
    result := -1;
  } else {
    var x := 0;
    while x <= k {
      var Px := x * x - x + c;
      var next_val := (x + 1) * (x + 1) - (x + 1) + c;
      if Px <= 0 && (x == 0 || next_val > 0) {
        result := k - x;
        return;
      }
      x := x + 1;
    }
    result := -1;
  }
}
// </vc-code>

