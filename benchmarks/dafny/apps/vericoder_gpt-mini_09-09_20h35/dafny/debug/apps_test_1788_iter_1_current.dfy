predicate ValidInput(a: int, b: int)
{
    -100 <= a <= 100 && -100 <= b <= 100 && (a + b) % 2 == 0 && (a - b) % 2 == 0
}

predicate CorrectSolution(a: int, b: int, x: int, y: int)
{
    a == x + y && b == x - y
}

// <vc-helpers>
lemma DivEven(n: int)
  requires n % 2 == 0
  ensures n == 2*(n/2)
{
  var q := n/2;
  assert n == q*2 + n%2;
  assert n%2 == 0;
  calc {
    n;
    == { }
    q*2 + n%2;
    == { }
    q*2;
  }
}

lemma Mul2ZeroImpliesZero(z: int)
  ensures (2*z == 0) ==> z == 0
{
  // Prove contrapositive: if z != 0 then 2*z != 0
  if z != 0 {
    if z > 0 {
      assert 2*z >= 2;
      assert 2*z != 0;
    } else {
      // z < 0
      assert 2*z <= -2;
      assert 2*z != 0;
    }
  }
}

lemma TwiceDivHalf(m: int)
  ensures (2*m)/2 == m
{
  var q := (2*m)/2;
  ghost DivEven(2*m);
  // From DivEven: 2*m == 2*q
  assert 2*m == 2*q;
  assert 2*(m - q) == 0;
  ghost Mul2ZeroImpliesZero(m - q);
  assert m - q == 0;
  assert q == m;
}

lemma SumDiv2(p: int, q: int)
  requires p % 2 == 0 && q % 2 == 0
  ensures p/2 + q/2 == (p + q)/2
{
  var pp := p/2;
  var qq := q/2;
  ghost DivEven(p);
  ghost DivEven(q);
  assert p == 2*pp;
  assert q == 2*qq;
  assert p + q == 2*(pp + qq);
  ghost DivEven(p + q);
  assert (p + q)/2 == pp + qq;
  assert p/2 + q/2 == (p + q)/2;
}

lemma DiffDiv2(p: int, q: int)
  requires p % 2 == 0 && q % 2 == 0
  ensures p/2 - q/2 == (p - q)/2
{
  var pp := p/2;
  var qq := q/2;
  ghost DivEven(p);
  ghost DivEven(q);
  assert p == 2*pp;
  assert q == 2*qq;
  assert p - q == 2*(pp - qq);
  ghost DivEven(p - q);
  assert (p - q)/2 == pp - qq;
  assert p/2 - q/2 == (p - q)/2;
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
  y := (a - b) / 2;

  ghost DivEven(a + b);
  ghost DivEven(a - b);

  ghost SumDiv2(a + b, a - b);
  ghost TwiceDivHalf(a);
  assert x + y == a;

  ghost DiffDiv2(a + b, a - b);
  ghost TwiceDivHalf(b);
  assert x - y == b;
}
// </vc-code>

