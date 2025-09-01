function fibfib(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 then 0
  else if n == 2 then 1
  else fibfib(n - 1) + fibfib(n - 2) + fibfib(n - 3)
}

// <vc-helpers>
function fibfib(n: nat): nat
    requires true
    ensures if n == 0 || n == 1 then fibfib(n) == 0
              else if n == 2 then fibfib(n) == 1
              else fibfib(n) == fibfib(n-1) + fibfib(n-2) + fibfib(n-3)
  decreases n
{
  if n == 0 || n == 1 then 0
  else if n == 2 then 1
  else fibfib(n - 1) + fibfib(n - 2) + fibfib(n - 3)
}
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
    var a := new nat[n + 1];
    a[0] := 0;
    a[1] := 0;
    a[2] := 1;
    var i := 3;
    while i <= n
      invariant 0 <= i <= n + 1
      invariant a[0] == 0 && a[1] == 0 && a[2] == 1
      invariant forall j :: 0 <= j < i ==> a[j] == fibfib(j)
    {
      a[i] := a[i - 1] + a[i - 2] + a[i - 3];
      i := i + 1;
    }
    result := a[n];
  }
}
// </vc-code>

