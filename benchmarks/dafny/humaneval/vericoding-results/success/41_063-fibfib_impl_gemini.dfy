// <vc-preamble>
function fibfib(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 then 0
  else if n == 2 then 1
  else fibfib(n - 1) + fibfib(n - 2) + fibfib(n - 3)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ComputeFibFib(n: nat) returns (result: nat)

  ensures result == fibfib(n)
// </vc-spec>
// <vc-code>
{
  if n <= 1 {
    result := 0;
  } else if n == 2 {
    result := 1;
  } else {
    var a: nat := 0;
    var b: nat := 0;
    var c: nat := 1;
    var i: nat := 2;
    while i < n
      invariant 2 <= i <= n
      invariant a == fibfib(i-2)
      invariant b == fibfib(i-1)
      invariant c == fibfib(i)
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
}
// </vc-code>
