function fib4_rec(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 || n == 2 then 0
  else if n == 3 then 1
  else fib4_rec(n - 1) + fib4_rec(n - 2) + fib4_rec(n - 3) + fib4_rec(n - 4)
}

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method fib4(n: nat) returns (result: nat)
  // post-conditions-start
  ensures result == fib4_rec(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
   if n <= 2 {
      return 0;
   } else if n == 3 {
      return 1;
   } else {
      var a0, a1, a2, a3 := 0, 0, 0, 1;
      var i := 4;
      while i <= n
          invariant 4 <= i <= n+1
          invariant a0 == fib4_rec(i-4) && a1 == fib4_rec(i-3) && a2 == fib4_rec(i-2) && a3 == fib4_rec(i-1)
      {
          var next := a0 + a1 + a2 + a3;
          a0, a1, a2, a3 := a1, a2, a3, next;
          i := i + 1;
      }
      return a3;
   }
}
// </vc-code>

