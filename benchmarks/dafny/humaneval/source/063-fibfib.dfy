function fibfib(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 then 0
  else if n == 2 then 1
  else fibfib(n - 1) + fibfib(n - 2) + fibfib(n - 3)
}
// pure-end
method ComputeFibFib(n: nat) returns (result: nat)
  // post-conditions-start
  ensures result == fibfib(n)
  // post-conditions-end
{
  // impl-start
  if n == 0 || n == 1 {
    return 0;
  }

  if n == 2 {
    return 1;
  }

  var a, b, c := 0, 0, 1;
  var i := 3;

  while i <= n
    // invariants-start
    invariant 3 <= i <= n + 1
    invariant a == fibfib(i-3)
    invariant b == fibfib(i-2)
    invariant c == fibfib(i-1)
    // invariants-end
  {
    var temp := c + b + a;
    a := b;
    b := c;
    c := temp;
    i := i + 1;
  }

  return c;
  // impl-end
}
