function fibfib(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 then 0
  else if n == 2 then 1
  else fibfib(n - 1) + fibfib(n - 2) + fibfib(n - 3)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ComputeFibFib(n: nat) returns (result: nat)
  // post-conditions-start
  ensures result == fibfib(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if n == 0 || n == 1 {
    result := 0;
  } else if n == 2 {
    result := 1;
  } else {
    var i := 3;
    var f0 := 0;
    var f1 := 0;
    var f2 := 1;
    while i <= n
      invariant 3 <= i <= n + 1
      invariant f0 == fibfib(i - 3)
      invariant f1 == fibfib(i - 2)
      invariant f2 == fibfib(i - 1)
      decreases n - i + 1
    {
      assert fibfib(i) == fibfib(i - 1) + fibfib(i - 2) + fibfib(i - 3);
      var next := f2 + f1 + f0;
      assert next == fibfib(i);
      f0 := f1;
      f1 := f2;
      f2 := next;
      i := i + 1;
    }
    result := f2;
  }
}
// </vc-code>

