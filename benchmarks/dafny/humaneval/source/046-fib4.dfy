function fib4_rec(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 || n == 2 then 0
  else if n == 3 then 1
  else fib4_rec(n - 1) + fib4_rec(n - 2) + fib4_rec(n - 3) + fib4_rec(n - 4)
}
// pure-end
method fib4(n: nat) returns (result: nat)
  // post-conditions-start
  ensures result == fib4_rec(n)
  // post-conditions-end
{
  // impl-start
  if n == 0 || n == 1 || n == 2 {
    return 0;
  }

  if n == 3 {
    return 1;
  }

  var a, b, c, d := 0, 0, 0, 1;
  var i := 4;

  while i <= n
    // invariants-start
    invariant 4 <= i <= n + 1
    invariant a == fib4_rec(i-4)
    invariant b == fib4_rec(i-3)
    invariant c == fib4_rec(i-2)
    invariant d == fib4_rec(i-1)
    // invariants-end
  {
    var temp := d + c + b + a;
    a := b;
    b := c;
    c := d;
    d := temp;
    i := i + 1;
  }

  return d;
  // impl-end
}
