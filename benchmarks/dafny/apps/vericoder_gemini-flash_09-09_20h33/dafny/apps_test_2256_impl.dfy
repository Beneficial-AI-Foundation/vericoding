predicate ValidInput(n: int, x: int, a: int, b: int)
{
    2 <= n <= 100 && 0 <= x <= 100 && 1 <= a <= n && 1 <= b <= n && a != b
}

function MaxDistance(n: int, x: int, a: int, b: int): int
    requires ValidInput(n, x, a, b)
{
    var initialDistance := if a >= b then a - b else b - a;
    var maxPossibleDistance := initialDistance + x;
    var maxLineDistance := n - 1;
    if maxPossibleDistance <= maxLineDistance then maxPossibleDistance else maxLineDistance
}

predicate ValidResult(n: int, x: int, a: int, b: int, result: int)
    requires ValidInput(n, x, a, b)
{
    result == MaxDistance(n, x, a, b) && 0 <= result <= n - 1
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SolveRivalDistance(n: int, x: int, a: int, b: int) returns (result: int)
    requires ValidInput(n, x, a, b)
    ensures ValidResult(n, x, a, b, result)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  var initialDistance := if a >= b then a - b else b - a;
  var maxPossibleDistance := initialDistance + x;
  var maxLineDistance := n - 1;
  result := if maxPossibleDistance <= maxLineDistance then maxPossibleDistance else maxLineDistance;

  // Proof for `result >= 0`
  assert initialDistance >= 0 by {
    if a >= b {
      calc {
        initialDistance;
        a - b;
      }
      // The original `because` clause was a parsing error.
      // Logical implication is `==>`, not `because`.
      // Also, `assert P by { ... }` is the correct syntax for assertion with a proof block.
      // No explicit `assert` statement with `because` keyword is needed inside the `by` block.
    } else { // b > a
      calc {
        initialDistance;
        b - a;
      }
    }
  }

  assert maxPossibleDistance >= initialDistance; // x >= 0 is given by valid input (0 <= x <= 100)
  assert maxPossibleDistance >= 0;

  assert maxLineDistance >= 0 by {
    calc {
      maxLineDistance;
      n - 1;
    }
  }

  if maxPossibleDistance <= maxLineDistance {
    assert result == maxPossibleDistance;
    assert result >= 0;
  } else {
    assert result == maxLineDistance;
    assert result >= 0;
  }

  // Proof for `result <= n - 1`
  if maxPossibleDistance <= maxLineDistance {
    assert result == maxPossibleDistance;
    assert result <= maxLineDistance;
    assert result <= n - 1;
  } else {
    assert result == maxLineDistance;
    assert result == n - 1;
  }
}
// </vc-code>

