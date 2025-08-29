function fib4_rec(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 || n == 2 then 0
  else if n == 3 then 1
  else fib4_rec(n - 1) + fib4_rec(n - 2) + fib4_rec(n - 3) + fib4_rec(n - 4)
}

// <vc-helpers>
lemma Fib4RecNonNegative(n: nat)
  ensures fib4_rec(n) >= 0
  decreases n
{
  if n == 0 || n == 1 || n == 2 {
    assert fib4_rec(n) == 0;
  } else if n == 3 {
    assert fib4_rec(n) == 1;
  } else {
    Fib4RecNonNegative(n - 1);
    Fib4RecNonNegative(n - 2);
    Fib4RecNonNegative(n - 3);
    Fib4RecNonNegative(n - 4);
    assert fib4_rec(n) == fib4_rec(n - 1) + fib4_rec(n - 2) + fib4_rec(n - 3) + fib4_rec(n - 4);
  }
}
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
    return 0;
  } else if n == 3 {
    return 1;
  }
  
  var f0 := 0;
  var f1 := 0;
  var f2 := 0;
  var f3 := 1;
  var i := 4;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant f0 == fib4_rec(i - 4)
    invariant f1 == fib4_rec(i - 3)
    invariant f2 == fib4_rec(i - 2)
    invariant f3 == fib4_rec(i - 1)
    decreases n - i
  {
    var next := f0 + f1 + f2 + f3;
    f0 := f1;
    f1 := f2;
    f2 := f3;
    f3 := next;
    i := i + 1;
  }
  return f3;
}
// </vc-code>
