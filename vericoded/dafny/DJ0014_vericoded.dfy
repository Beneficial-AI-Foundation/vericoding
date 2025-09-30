// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
    invariant forall k:int :: 0 <= k < i ==> a[k] % 2 == N % 2
    modifies a
  {
    if N % 2 == 0 {
      if a[i] % 2 == 1 {
        a[i] := a[i] + 1;
      }
    } else {
      if a[i] % 2 == 0 {
        a[i] := a[i] + 1;
      }
    }
    i := i + 1;
  }
}
// </vc-code>
