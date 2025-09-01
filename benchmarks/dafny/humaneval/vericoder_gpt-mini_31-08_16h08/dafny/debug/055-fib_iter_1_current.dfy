function fib(n: nat): nat
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ComputeFib(n: nat) returns (result: nat)
  // post-conditions-start
  ensures result == fib(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    result := 0;
    return;
  }
  var a := 0;
  var b := 1;
  var i := 1;
  while i < n
    invariant 1 <= i <= n && a == fib(i - 1) && b == fib(i)
    decreases n - i
  {
    var next := a + b;
    a := b;
    b := next;
    i := i + 1;
  }
  result := b;
}
// </vc-code>

