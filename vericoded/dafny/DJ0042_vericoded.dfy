// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
    requires N > 0
    requires a.Length == N
    requires sum.Length == 1
    requires N < 1000
    ensures sum[0] == 5 * N
    modifies a, sum
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant forall j :: 0 <= j < i ==> a[j] == 5
  {
    a[i] := 5;
    i := i + 1;
  }
  
  var total := 0;
  i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant total == 5 * i
    invariant forall j :: 0 <= j < N ==> a[j] == 5
  {
    total := total + a[i];
    i := i + 1;
  }
  
  sum[0] := total;
}
// </vc-code>
