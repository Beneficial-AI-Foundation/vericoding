function fib(n: nat): nat
decreases n
{
   if n == 0 then 0 else
   if n == 1 then 1 else
                  fib(n - 1) + fib(n - 2)
}

// <vc-helpers>
lemma fib_correctness(a: nat, b: nat, n: nat, k: nat)
  requires k <= n
  requires a == fib(k)
  requires b == fib(k + 1)
  ensures fib(n) == fibonacci_loop(a, b, k, n)
  decreases n - k
{
  if k == n {
    assert fib(n) == a;
  } else {
    assert k < n;
    fibonacci_loop_step(a, b, k, n);
  }
}

lemma fibonacci_loop_step(a: nat, b: nat, k: nat, n: nat)
  requires k < n
  requires a == fib(k)
  requires b == fib(k + 1)
  ensures fibonacci_loop(a, b, k, n) == fibonacci_loop(b, a + b, k + 1, n)
{
  // This follows from the definition of fibonacci_loop
}

function fibonacci_loop(a: nat, b: nat, k: nat, n: nat): nat
  requires k <= n
  decreases n - k
{
  if k == n then a
  else fibonacci_loop(b, a + b, k + 1, n)
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method fibonacci1(n:nat) returns (f:nat)
ensures f==fib(n)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  if n == 0 {
    f := 0;
  } else if n == 1 {
    f := 1;
  } else {
    var a := 0;
    var b := 1;
    var i := 2;
    
    while i <= n
      invariant 2 <= i <= n + 1
      invariant a == fib(i - 2)
      invariant b == fib(i - 1)
      decreases n - i + 1
    {
      var temp := a + b;
      a := b;
      b := temp;
      i := i + 1;
    }
    
    f := b;
  }
}
// </vc-code>
