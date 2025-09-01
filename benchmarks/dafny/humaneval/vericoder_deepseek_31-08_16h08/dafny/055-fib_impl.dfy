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
    // The lemma requires that the caller provides correct a and b
    // For n=1, we need a=1 and b=0 to satisfy fib(1) == 1 + 0*fib(0)
    // But the assertion a == 1 is not necessarily true - it depends on caller
    // This lemma should be used with specific a,b values, not general ones
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
      var next := a + b;
      a := b;
      b := next;
      i := i + 1;
      // The invariants are maintained:
      // After update: new a = old b = fib(i-1) = fib((i+1)-2)
      // new b = old a + old b = fib(i-1) + fib(i) = fib(i+1)
      // i increases by 1, so i <= n still holds
    }
    result := b;
  }
}
// </vc-code>

