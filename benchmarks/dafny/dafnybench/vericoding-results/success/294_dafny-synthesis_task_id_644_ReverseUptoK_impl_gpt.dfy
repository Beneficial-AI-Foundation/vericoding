

// <vc-helpers>
// <vc-helpers>

// </vc-helpers>
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
  var i := 0;
  while i < k / 2
    invariant 0 <= i <= k / 2
    invariant forall j :: k <= j < s.Length ==> s[j] == old(s[j])
    invariant forall j :: 0 <= j < i ==> s[j] == old(s[k - 1 - j])
    invariant forall j :: 0 <= j < i ==> s[k - 1 - j] == old(s[j])
    invariant forall j :: i <= j < k - i ==> s[j] == old(s[j])
    decreases k / 2 - i
  {
    var tmp := s[i];
    s[i] := s[k - 1 - i];
    s[k - 1 - i] := tmp;
    i := i + 1;
  }
}
// </vc-code>

