// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Zero(): int { 0 }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, N: int, m: int)
	requires N > 0
	requires a.Length == N
	modifies a
	ensures forall k :: 0 <= k < N ==> a[k] <= N
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant forall k :: 0 <= k < i ==> a[k] <= N
  {
    a[i] := 0;
    i := i + 1;
  }
}
// </vc-code>
