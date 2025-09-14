// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsValidArrayIndex(arr: array<int>, index: int) {
  0 <= index < arr.Length
}
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
	requires
		N > 0 &&
		a.Length == N &&
		sum.Length == 1
	modifies a, sum
	ensures
		sum[0] == N
// </vc-spec>
// <vc-code>
{
  sum[0] := N;
}
// </vc-code>
