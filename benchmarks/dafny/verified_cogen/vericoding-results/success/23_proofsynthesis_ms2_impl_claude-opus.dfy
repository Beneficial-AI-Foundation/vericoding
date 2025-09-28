// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int) 
	requires a.Length == N && sum.Length == 1 && N > 0
	modifies a, sum
	ensures sum[0] <= N
// </vc-spec>
// <vc-code>
{
  var count := 0;
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant count <= i
  {
    if a[i] == 1 {
      count := count + 1;
    }
    i := i + 1;
  }
  sum[0] := count;
}
// </vc-code>
