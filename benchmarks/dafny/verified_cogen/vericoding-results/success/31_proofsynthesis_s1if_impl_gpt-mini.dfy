// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SeqLen(s: seq<int>): int { |s| }
predicate ValidInput(a: array<int>, sum: array<int>, N: int) { N > 0 && a.Length == N && sum.Length == 1 }
lemma InputProps(a: array<int>, sum: array<int>, N: int)
  requires ValidInput(a, sum, N)
  ensures a.Length == N && sum.Length == 1
{ }
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
