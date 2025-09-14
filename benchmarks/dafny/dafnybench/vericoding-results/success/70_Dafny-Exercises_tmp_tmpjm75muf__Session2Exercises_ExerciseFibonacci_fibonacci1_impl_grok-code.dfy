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
  if n == 0 { f := 0; }
  else if n == 1 { f := 1; }
  else {
    var f1 := fibonacci1(n-1);
    var f2 := fibonacci1(n-2);
    f := f1 + f2;
  }
}
// </vc-code>

