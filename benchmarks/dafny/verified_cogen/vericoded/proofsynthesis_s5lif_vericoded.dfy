// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
	requires
		N > 0 &&
		a.Length == N &&
		sum.Length == 1 &&
		N < 1000

	ensures
		sum[0] == 6 * N
	modifies a, sum
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant forall j :: 0 <= j < i ==> a[j] == 6
    modifies a
  {
    a[i] := 6;
    i := i + 1;
  }
  
  var total := 0;
  i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant total == 6 * i
  {
    total := total + a[i];
    i := i + 1;
  }
  
  sum[0] := total;
}
// </vc-code>
