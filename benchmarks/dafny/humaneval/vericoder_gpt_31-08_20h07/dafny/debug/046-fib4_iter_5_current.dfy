function fib4_rec(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 || n == 2 then 0
  else if n == 3 then 1
  else fib4_rec(n - 1) + fib4_rec(n - 2) + fib4_rec(n - 3) + fib4_rec(n - 4)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method fib4(n: nat) returns (result: nat)
  // post-conditions-start
  ensures result == fib4_rec(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if n == 0 || n == 1 || n == 2 {
    result := 0;
  } else if n == 3 {
    result := 1;
  } else {
    var i: nat := 4;
    var a0: nat := 0;
    var a1: nat := 0;
    var a2: nat := 0;
    var a3: nat := 1;
    while i <= n
      invariant 4 <= i
      invariant i <= n + 1
      invariant a0 == fib4_rec(i - 4)
      invariant a1 == fib4_rec(i - 3)
      invariant a2 == fib4_rec(i - 2)
      invariant a3 == fib4_rec(i - 1)
      decreases n - i
    {
      var next: nat := a0 + a1 + a2 + a3;
      assert i >= 4;
      assert fib4_rec(i) ==
        fib4_rec(i - 1) + fib4_rec(i - 2) + fib4_rec(i - 3) + fib4_rec(i - 4);
      a0, a1, a2, a3 := a1, a2, a3, next;
      i := i + 1;
    }
    result := a3;
  }
}
// </vc-code>

