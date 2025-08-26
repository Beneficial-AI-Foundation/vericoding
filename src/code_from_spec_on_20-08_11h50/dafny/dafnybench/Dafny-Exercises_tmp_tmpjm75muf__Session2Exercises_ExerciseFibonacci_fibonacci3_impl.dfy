// <vc-spec>
function fib(n: nat): nat
decreases n
{
   if n == 0 then 0 else
   if n == 1 then 1 else
                  fib(n - 1) + fib(n - 2)
}

// <vc-helpers>
// </vc-helpers>

method fibonacci3(n:nat) returns (f:nat)
ensures f==fib(n)
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