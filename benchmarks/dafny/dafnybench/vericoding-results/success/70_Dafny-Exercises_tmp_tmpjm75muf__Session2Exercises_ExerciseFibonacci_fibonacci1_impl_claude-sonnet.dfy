function fib(n: nat): nat
decreases n
{
   if n == 0 then 0 else
   if n == 1 then 1 else
                  fib(n - 1) + fib(n - 2)
}

// <vc-helpers>
lemma FibCorrectness(a: nat, b: nat, i: nat, n: nat)
  requires i <= n
  requires a == fib(i)
  requires b == fib(i + 1)
  ensures fib(n) == FibHelper(a, b, i, n)
  decreases n - i
{
  if i == n {
    assert fib(n) == a;
  } else {
    FibCorrectness(b, a + b, i + 1, n);
  }
}

function FibHelper(a: nat, b: nat, i: nat, n: nat): nat
  requires i <= n
  decreases n - i
{
  if i == n then a
  else FibHelper(b, a + b, i + 1, n)
}
// </vc-helpers>

// <vc-spec>
method fibonacci1(n:nat) returns (f:nat)
ensures f==fib(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    return 0;
  } else if n == 1 {
    return 1;
  } else {
    var a := 0;
    var b := 1;
    var i := 0;
    
    while i < n
      invariant i <= n
      invariant a == fib(i)
      invariant b == fib(i + 1)
      decreases n - i
    {
      var temp := a + b;
      a := b;
      b := temp;
      i := i + 1;
    }
    
    return a;
  }
}
// </vc-code>

