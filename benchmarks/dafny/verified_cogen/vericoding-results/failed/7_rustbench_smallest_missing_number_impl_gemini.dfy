// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SmallestMissingNumber(s: array<int>) returns (v: int)
    requires forall i, j :: 0 <= i < j < s.Length ==> s[i] <= s[j]
    requires forall i :: 0 <= i < s.Length ==> s[i] >= 0
    requires s.Length <= 100_000
    ensures 0 <= v
    ensures forall i :: 0 <= i < s.Length ==> s[i] != v
    ensures forall k {:trigger} :: 0 <= k < v ==> exists j :: 0 <= j < s.Length && s[j] == k
// </vc-spec>
// <vc-code>
{
  v := 0;
  var i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant 0 <= v
    invariant forall k :: 0 <= k < v ==> exists j :: 0 <= j < i && s[j] == k
    invariant forall j :: 0 <= j < i ==> s[j] < v
  {
    if s[i] == v {
      v := v + 1;
    } else if s[i] > v {
      assert forall k :: 0 <= k < v ==> exists j :: 0 <= j < s.Length && s[j] == k;
      assert forall j :: 0 <= j < s.Length ==> s[j] != v;
      return;
    }
    i := i + 1;
  }
  assert forall k :: 0 <= k < v ==> exists j :: 0 <= j < s.Length && s[j] == k;
  assert forall j :: 0 <= j < s.Length ==> s[j] != v;
}
// </vc-code>
