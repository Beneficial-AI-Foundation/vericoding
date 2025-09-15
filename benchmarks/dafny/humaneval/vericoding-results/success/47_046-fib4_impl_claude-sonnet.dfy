// <vc-preamble>
function fib4_rec(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 || n == 2 then 0
  else if n == 3 then 1
  else fib4_rec(n - 1) + fib4_rec(n - 2) + fib4_rec(n - 3) + fib4_rec(n - 4)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method fib4(n: nat) returns (result: nat)

  ensures result == fib4_rec(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 || n == 1 || n == 2 {
    result := 0;
  } else if n == 3 {
    result := 1;
  } else {
    var a := 0;
    var b := 0;
    var c := 0;
    var d := 1;
    var i := 4;
    while i <= n
      invariant 4 <= i <= n + 1
      invariant a == fib4_rec(i - 4)
      invariant b == fib4_rec(i - 3)
      invariant c == fib4_rec(i - 2)
      invariant d == fib4_rec(i - 1)
    {
      var next := a + b + c + d;
      a := b;
      b := c;
      c := d;
      d := next;
      i := i + 1;
    }
    result := d;
  }
}
// </vc-code>
