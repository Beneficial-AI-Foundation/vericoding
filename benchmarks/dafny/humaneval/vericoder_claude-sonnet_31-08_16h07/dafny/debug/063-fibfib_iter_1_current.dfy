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
    var f1 := ComputeFibFib(n - 1);
    var f2 := ComputeFibFib(n - 2);
    var f3 := ComputeFibFib(n - 3);
    result := f1 + f2 + f3;
  }
}
// </vc-code>

