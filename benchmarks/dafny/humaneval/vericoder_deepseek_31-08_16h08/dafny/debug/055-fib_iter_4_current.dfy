function fib(n: nat): nat
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

// <vc-helpers>
lemma FibLemma(n: nat, a: nat, b: nat)
  requires n >= 1
  ensures fib(n) == a + b * fib(n-1)
{
  if n == 1 {
    assert fib(1) == 1 && fib(0) == 0;
    assert a + b * fib(0) == a + b * 0 == a;
    assert a == 1;
  } else if n >= 2 {
    FibLemma(n-1, b, a + b);
  }
}

lemma FibIdentity(n: nat)
  ensures fib(n+2) == fib(n+1) + fib(n)
{
}

lemma FibLoopInvariant(i: nat, n: nat, a: nat, b: nat)
  requires 1 <= i <= n
  requires a == fib(i-1) && b == fib(i)
  ensures if i < n then fib(i+1) == a + b else true
{
  if i < n {
    FibIdentity(i-1);
    assert fib(i+1) == fib(i) + fib(i-1) == b + a;
  }
}
// </vc-helpers>

// <vc-spec>
method ComputeFib(n: nat) returns (result: nat)
  // post-conditions-start
  ensures result == fib(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    result := 0;
  } else if n == 1 {
    result := 1;
  } else {
    var a := 0;
    var b := 1;
    var i := 1;
    while i < n
      invariant 1 <= i <= n
      invariant a == fib(i-1)
      invariant b == fib(i)
    {
      FibLoopInvariant(i, n, a, b);
      var next := a + b;
      a := b;
      b := next;
      i := i + 1;
    }
    result := b;
  }
}
// </vc-code>

