function fib(n: nat): nat
decreases n
{
   if n == 0 then 0 else
   if n == 1 then 1 else
                  fib(n - 1) + fib(n - 2)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method fibonacci1(n:nat) returns (f:nat)
ensures f==fib(n)
// </vc-spec>
// <vc-code>
{
  var a := 0;
  var b := 1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant a == fib(i)
    invariant b == fib(i + 1)
    decreases n - i
  {
    var anew := b;
    var bnew := a + b;
    a := anew;
    b := bnew;
    i := i + 1;
  }
  f := a;
}
// </vc-code>

