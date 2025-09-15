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
function fib4_helper(n: nat): nat
  ensures fib4_helper(n) == fib4_rec(n)
  decreases n
{
  if n == 0 || n == 1 || n == 2 then 0
  else if n == 3 then 1
  else fib4_helper(n - 1) + fib4_helper(n - 2) + fib4_helper(n - 3) + fib4_helper(n - 4)
}
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
    var a := fib4(n - 1);
    var b := fib4(n - 2);
    var c := fib4(n - 3);
    var d := fib4(n - 4);
    result := a + b + c + d;
  }
}
// </vc-code>
