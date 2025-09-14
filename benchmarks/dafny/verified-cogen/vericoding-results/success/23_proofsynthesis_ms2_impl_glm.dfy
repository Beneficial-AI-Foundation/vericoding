// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate ValidIndex(a: array<int>, i: int) { 0 <= i < a.Length }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int) 
	requires a.Length == N && sum.Length == 1 && N > 0
	modifies a, sum
	ensures sum[0] <= N
// </vc-spec>
// <vc-code>
{
  var total := 0;
  var i := 0;
  while i < N
    invariant 0 <= i <= N
  {
    a[i] := i;
    total := total + a[i];
    i := i + 1;
  }
  sum[0] := total % (N + 1);
}
// </vc-code>
