predicate ValidInput(n: int, a: int, b: int) {
    n >= 1 && 1 <= a <= n && -100 <= b <= 100
}

function FinalEntrance(n: int, a: int, b: int): int
    requires ValidInput(n, a, b)
{
    ((a - 1 + b) % n + n) % n + 1
}

predicate ValidOutput(result: int, n: int) {
    1 <= result <= n
}

// <vc-helpers>
lemma ModLemma(n: int, a: int, b: int)
  requires ValidInput(n, a, b)
  ensures ((a - 1 + b) % n + n) % n + 1 >= 1
  ensures ((a - 1 + b) % n + n) % n + 1 <= n
{
  var x := a - 1 + b;
  var y := x % n;
  var z := (y + n) % n;
  var result := z + 1;
  
  // Prove result >= 1
  assert z >= 0 by {
    if y >= 0 {
      assert z == y;
    } else {
      assert z == y + n;
      assert z >= 0;
    }
  };
  assert result >= 1;
  
  // Prove result <= n
  assert z <= n - 1 by {
    assert -n < y < n;
    if y >= 0 {
      assert z == y < n;
    } else {
      assert z == y + n;
      assert z < n;
    }
  };
  assert result <= n;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int) returns (result: int)
    requires ValidInput(n, a, b)
    ensures ValidOutput(result, n)
    ensures result == FinalEntrance(n, a, b)
// </vc-spec>
// <vc-code>
{
  var x := a - 1 + b;
  var y := x % n;
  var z := (y + n) % n;
  result := z + 1;
}
// </vc-code>

