predicate ValidInput(a: int, b: int)
{
    -100 <= a <= 100 && -100 <= b <= 100 && (a + b) % 2 == 0 && (a - b) % 2 == 0
}

predicate CorrectSolution(a: int, b: int, x: int, y: int)
{
    a == x + y && b == x - y
}

// <vc-helpers>
lemma evenHalfDouble(n: int)
  requires n % 2 == 0
  ensures 2 * (n / 2) == n
{
  assert n == 2 * (n / 2) + n % 2;
  assert n % 2 == 0;
  assert 2 * (n / 2) == n;
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (x: int, y: int)
    requires ValidInput(a, b)
    ensures CorrectSolution(a, b, x, y)
// </vc-spec>
// <vc-code>
{
  x := (a + b) / 2;
  y := a - x;

  calc {
    x + y;
    == { }
    x + (a - x);
    == { }
    a;
  }

  evenHalfDouble(a + b);

  calc {
    x - y;
    == { }
    x - (a - x);
    == { }
    2 * x - a;
    == { }
    2 * ((a + b) / 2) - a;
    == { }
    (a + b) - a;
    == { }
    b;
  }
}
// </vc-code>

