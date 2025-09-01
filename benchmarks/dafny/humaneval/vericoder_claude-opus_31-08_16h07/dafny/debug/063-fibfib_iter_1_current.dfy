function fibfib(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 then 0
  else if n == 2 then 1
  else fibfib(n - 1) + fibfib(n - 2) + fibfib(n - 3)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ComputeFibFib(n: nat) returns (result: nat)
  // post-conditions-start
  ensures result == fibfib(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if n == 0 || n == 1 {
    return 0;
  }
  if n == 2 {
    return 1;
  }
  
  var a := 0; // fibfib(0)
  var b := 0; // fibfib(1) 
  var c := 1; // fibfib(2)
  
  var i := 3;
  while i <= n
    invariant 3 <= i <= n + 1
    invariant a == fibfib(i - 3)
    invariant b == fibfib(i - 2)
    invariant c == fibfib(i - 1)
  {
    var next := a + b + c;
    a := b;
    b := c;
    c := next;
    i := i + 1;
  }
  
  return c;
}
// </vc-code>

