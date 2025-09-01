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
    // fib(1) = 1, fib(0) = 0
    // 1 == 1 + 0 * fib(0)
  } else if n >= 2 {
    FibLemma(n-1, b, a - b);
    // fib(n) = fib(n-1) + fib(n-2)
    // = fib(n-1) + (fib(n-1) - fib(n-3))? 
    // Alternative approach: use the mathematical definition directly
    assert fib(n) == fib(n-1) + fib(n-2);
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
    }
    result := b;
  }
}
// </vc-code>

