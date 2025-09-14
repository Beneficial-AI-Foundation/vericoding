

// <vc-helpers>
// No helpers required for this proof.
// </vc-helpers>

// <vc-spec>
method ReverseUptoK(s: array<int>, k: int)
    modifies s
    requires 2 <= k <= s.Length
    ensures forall i :: 0 <= i < k ==> s[i] == old(s[k - 1 - i])
    ensures forall i :: k <= i < s.Length ==> s[i] == old(s[i])
// </vc-spec>
// <vc-code>
{
  ghost var orig := s[..];
  var lo := 0;
  var hi := k - 1;
  while lo < hi
    invariant 0 <= lo <= k
    invariant -1 <= hi < k
    invariant lo + hi == k - 1
    invariant forall i :: 0 <= i < lo ==> s[i] == orig[k - 1 - i]
    invariant forall i :: hi < i < k ==> s[i] == orig[k - 1 - i]
    invariant forall i :: lo <= i <= hi ==> s[i] == orig[i]
    invariant forall i :: k <= i < s.Length ==> s[i] == orig[i]
  {
    var tmp := s[lo];
    s[lo] := s[hi];
    s[hi] := tmp;
    lo := lo + 1;
    hi := hi - 1;
  }
}
// </vc-code>

