predicate ValidInput(n: int, a: int, b: int, c: int)
{
  1 <= n <= 100 && 1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100
}

function MinDistance(n: int, a: int, b: int, c: int): int
  requires ValidInput(n, a, b, c)
  ensures MinDistance(n, a, b, c) >= 0
  ensures n == 1 ==> MinDistance(n, a, b, c) == 0
{
  if n == 1 then 0
  else (n - 1) * min(a, b)
}

function min(x: int, y: int): int
{
  if x <= y then x else y
}

function max(x: int, y: int): int
{
  if x >= y then x else y
}

// <vc-helpers>
lemma MinLeMax(a:int, b:int, c:int)
  ensures min(a,b) <= max(a, max(b,c))
{
  if a <= b {
    assert min(a,b) == a;
    assert a <= max(a, max(b,c));
  } else {
    assert min(a,b) == b;
    assert b <= max(a, max(b,c));
  }
}

lemma MinAtLeastOne(a:int, b:int)
  requires a >= 1
  requires b >= 1
  ensures min(a,b) >= 1
{
  if a <= b {
    assert min(a,b) == a;
    assert a >= 1;
  } else {
    assert min(a,b) == b;
    assert b >= 1;
  }
}

lemma MulLeMonotonic(k:int, x:int, y:int)
  requires k >= 0
  requires x <= y
  ensures k * x <= k * y
  decreases k
{
  if k == 0 {
    // 0 * x <= 0 * y holds
  } else {
    MulLeMonotonic(k-1, x, y);
    assert (k-1) * x <= (k-1) * y;
    assert x <= y;
    assert (k-1) * x + x <= (k-1) * y + y;
    assert k * x <= k * y;
  }
}

lemma MulNonneg(k:int, x:int)
  requires k >= 0
  requires x >= 0
  ensures k * x >= 0
  decreases k
{
  if k == 0 {
    // 0 * x >= 0
  } else {
    MulNonneg(k-1, x);
    assert (k-1) * x >= 0;
    assert x >= 0;
    assert (k-1) * x + x >= 0;
    assert k * x >= 0;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int, c: int) returns (result: int)
  requires ValidInput(n, a, b, c)
  ensures result >= 0
  ensures n == 1 ==> result == 0
  ensures result <= (n-1) * max(a, max(b, c))
  ensures result == MinDistance(n, a, b, c)
// </vc-spec>
// <vc-code>
{
  if n == 1 {
    result := 0;
  } else {
    result := (n - 1) * min(a, b);
  }

  // result equals the specification function
  assert result == MinDistance(n, a, b, c);

  // result >= 0
  if n == 1 {
    assert result >= 0;
  } else {
    assert n - 1 >= 0;
    MinAtLeastOne(a, b);
    MulNonneg(n - 1, min(a, b));
    assert result >= 0;
  }

  // result <= (n-1) * max(a, max(b, c))
  if n == 1 {
    // both sides are 0
    assert result <= (n - 1) * max(a, max(b, c));
  } else {
    MinLeMax(a, b, c);
    MulLeMonotonic(n - 1, min(a, b), max(a, max(b, c)));
    assert result <= (n - 1) * max(a, max(b, c));
  }
}
// </vc-code>

