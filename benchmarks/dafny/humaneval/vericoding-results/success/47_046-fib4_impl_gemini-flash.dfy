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
/* helper modified by LLM (iteration 4): This helper function is redundant as the base cases are handled directly in the `fib4` method. */
function fib4_iter_base(n: nat): nat
  requires n >= 0
{
  if n == 0 || n == 1 || n == 2 then 0
  else if n == 3 then 1
  else 0
}
// </vc-helpers>

// <vc-spec>
method fib4(n: nat) returns (result: nat)

  ensures result == fib4_rec(n)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed compilation error by adding an opening brace for the `then` clause and removed the redundant `fib4_iter_base` helper call. The base cases are now directly handled within the method. */
{
  if n == 0 || n == 1 || n == 2 {
    result := 0;
  } else if n == 3 {
    result := 1;
  } else {
    var a0 := 0; // fib4_rec(i-4)
    var a1 := 0; // fib4_rec(i-3)
    var a2 := 0; // fib4_rec(i-2)
    var a3 := 1; // fib4_rec(i-1)

    var i := 4;
    while i <= n
      invariant 0 <= i <= n + 1
      invariant a0 == fib4_rec(i - 4)
      invariant a1 == fib4_rec(i - 3)
      invariant a2 == fib4_rec(i - 2)
      invariant a3 == fib4_rec(i - 1)
    {
      var next_fib := a0 + a1 + a2 + a3;
      a0 := a1;
      a1 := a2;
      a2 := a3;
      a3 := next_fib;
      i := i + 1;
    }
    result := a3;
  }
}
// </vc-code>
