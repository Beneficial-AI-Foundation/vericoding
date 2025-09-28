// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function identity(x: int): int { x }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, N: int)
    requires N > 0
    requires a.Length == N
    ensures forall k:int :: 0 <= k < N ==> a[k] % 2 == N % 2
    modifies a
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant a.Length == N
    invariant forall k:int :: 0 <= k < i ==> a[k] % 2 == N % 2
  {
    a[i] := N;
    i := i + 1;
  }
}
// </vc-code>
