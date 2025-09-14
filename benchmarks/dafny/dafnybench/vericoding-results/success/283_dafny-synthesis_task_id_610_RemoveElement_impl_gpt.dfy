

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method RemoveElement(s: array<int>, k: int) returns (v: array<int>)
    requires 0 <= k < s.Length
    ensures v.Length == s.Length - 1
    ensures forall i :: 0 <= i < k ==> v[i] == s[i]
    ensures forall i :: k <= i < v.Length ==> v[i] == s[i + 1]
// </vc-spec>
// <vc-code>
{
  v := new int[s.Length - 1];
  assert k <= v.Length;
  var i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant forall j :: 0 <= j < i && j < k ==> v[j] == s[j]
    invariant forall j :: 0 <= j < i && k <= j ==> v[j] == s[j + 1]
    decreases v.Length - i
  {
    if i < k {
      v[i] := s[i];
    } else {
      assert i + 1 < s.Length;
      v[i] := s[i + 1];
    }
    i := i + 1;
  }
}
// </vc-code>

