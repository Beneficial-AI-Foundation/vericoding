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

method fibonacci2(n:nat) returns (f:nat)
ensures f==fib(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    f := 0;
    return;
  }
  if n == 1 {
    f := 1;
    return;
  }
  
  var prev := 0;
  var curr := 1;
  var i := 2;
  
  while i <= n
    invariant 2 <= i <= n + 1
    invariant prev == fib(i - 2)
    invariant curr == fib(i - 1)
  {
    var next := prev + curr;
    prev := curr;
    curr := next;
    i := i + 1;
  }
  
  f := curr;
}
// </vc-code>