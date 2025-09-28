// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

lemma HelperLemma(x: int)
  ensures x % 2 == 0 ==> x * 2 % 2 == 0
  ensures x % 2 == 1 ==> x * 2 % 2 == 0
{
}

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
  {
    var target_parity := N % 2;
    if a[i] % 2 != target_parity {
      a[i] := a[i] + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
