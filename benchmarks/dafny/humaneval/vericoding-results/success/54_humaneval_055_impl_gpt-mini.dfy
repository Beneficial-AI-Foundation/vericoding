// <vc-preamble>

predicate ValidInput(n: int) {
    n > 0
}

function fib_spec(n: int): int
    requires n > 0
{
    if n == 1 then 1
    else if n == 2 then 1
    else fib_spec(n-1) + fib_spec(n-2)
}
// </vc-preamble>

// <vc-helpers>
lemma FibSpecStep(k: int)
  requires k >= 1
  ensures fib_spec(k+2) == fib_spec(k+1) + fib_spec(k)
{
  assert fib_spec(k+2) == fib_spec(k+1) + fib_spec(k);
}

lemma FibSpecPositive(n: int)
  requires n > 0
  ensures fib_spec(n) > 0
  decreases n
{
  if n == 1 || n == 2 {
    // base cases: fib_spec(1) == 1, fib_spec(2) == 1
  } else {
    FibSpecPositive(n-1);
    FibSpecPositive(n-2);
    assert fib_spec(n) == fib_spec(n-1) + fib_spec(n-2);
    assert fib_spec(n-1) + fib_spec(n-2) > 0;
  }
}

// </vc-helpers>

// <vc-spec>
method fib(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == fib_spec(n)
    ensures result > 0
// </vc-spec>
// <vc-code>
{
  var k := 1;
  var a := 1;
  var b := 1;
  while k < n
    invariant 1 <= k <= n
    invariant a == fib_spec(k)
    invariant b == fib_spec(k+1)
  {
    var t := a + b;
    FibSpecStep(k);
    a := b;
    b := t;
    k := k + 1;
  }
  FibSpecPositive(n);
  result := a;
}

// </vc-code>
