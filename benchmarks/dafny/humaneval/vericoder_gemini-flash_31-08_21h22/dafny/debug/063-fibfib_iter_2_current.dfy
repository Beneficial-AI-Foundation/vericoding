function fibfib(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 then 0
  else if n == 2 then 1
  else fibfib(n - 1) + fibfib(n - 2) + fibfib(n - 3)
}

// <vc-helpers>
function fibfib(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 then 0
  else if n == 2 then 1
  else fibfib(n - 1) + fibfib(n - 2) + fibfib(n - 3)
}
// </vc-helpers>

// <vc-spec>
method ComputeFibFib(n: nat) returns (result: nat)
  // post-conditions-start
  ensures result == fibfib(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if n == 0 || n == 1 then result := 0
  else if n == 2 then result := 1
  else
    var a := 0; // fibfib(i-3)
    var b := 0; // fibfib(i-2)
    var c := 1; // fibfib(i-1)
    var i := 3;
    while i <= n
      invariant 3 <= i <= n + 1
      invariant a == fibfib(i-3)
      invariant b == fibfib(i-2)
      invariant c == fibfib(i-1)
      decreases n - i
    {
      var next_c := a + b + c;
      a := b;
      b := c;
      c := next_c;
      i := i + 1;
    }
    result := c;
}
// </vc-code>

