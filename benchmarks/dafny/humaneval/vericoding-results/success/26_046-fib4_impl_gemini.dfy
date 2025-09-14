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
  if n <= 2 {
    result := 0;
  } else if n == 3 {
    result := 1;
  } else {
    var i: nat := 3;
    var a: nat := 0; // fib4_rec(0)
    var b: nat := 0; // fib4_rec(1)
    var c: nat := 0; // fib4_rec(2)
    var d: nat := 1; // fib4_rec(3)
    
    while i < n
      invariant 3 <= i <= n
      invariant a == fib4_rec(i-3)
      invariant b == fib4_rec(i-2)
      invariant c == fib4_rec(i-1)
      invariant d == fib4_rec(i)
      decreases n - i
    {
      var next_d := a + b + c + d;
      a, b, c, d := b, c, d, next_d;
      i := i + 1;
    }
    
    result := d;
  }
}
// </vc-code>
