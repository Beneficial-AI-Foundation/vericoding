

// <vc-helpers>
// No additional helpers needed for this verification.
// </vc-helpers>

// <vc-spec>
method SmallestMissingNumber(s: seq<int>) returns (v: int)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    ensures 0 <= v
    ensures v !in s
    ensures forall k :: 0 <= k < v ==> k in s
// </vc-spec>
// <vc-code>
{
  var m := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= m
    invariant forall k :: 0 <= k < m ==> k in s
    invariant forall k :: 0 <= k < i ==> s[k] < m
  {
    if s[i] == m {
      m := m + 1;
      i := i + 1;
    } else if s[i] > m {
      return m;
    } else {
      i := i + 1;
    }
  }
  return m;
}
// </vc-code>

