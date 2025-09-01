function fib4_rec(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 || n == 2 then 0
  else if n == 3 then 1
  else fib4_rec(n - 1) + fib4_rec(n - 2) + fib4_rec(n - 3) + fib4_rec(n - 4)
}

// <vc-helpers>
// No helper lemmas required for this proof.
// </vc-helpers>

// <vc-spec>
method fib4(n: nat) returns (result: nat)
  // post-conditions-start
  ensures result == fib4_rec(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if n < 4 {
    if n == 3 {
      result := 1;
    } else {
      result := 0;
    }
    return;
  }

  var a := 0; // fib4_rec(0)
  var b := 0; // fib4_rec(1)
  var c := 0; // fib4_rec(2)
  var d := 1; // fib4_rec(3)
  var i := 4;
  while i <= n
    invariant 4 <= i <= n + 1
    invariant a == fib4_rec(i - 4)
    invariant b == fib4_rec(i - 3)
    invariant c == fib4_rec(i - 2)
    invariant d == fib4_rec(i - 1)
    decreases n - i
  {
    var e := a + b + c + d;
    assert e == fib4_rec(i); // by definition of fib4_rec for i >= 4
    a, b, c, d := b, c, d, e;
    i := i + 1;
  }
  result := d;
}
// </vc-code>

