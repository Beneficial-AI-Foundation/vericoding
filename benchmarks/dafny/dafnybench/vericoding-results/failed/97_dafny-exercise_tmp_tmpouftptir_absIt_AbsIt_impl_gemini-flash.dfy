

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method AbsIt(s: array<int>) 
modifies s
ensures forall i :: 0 <= i < s.Length ==> if old(s[i]) < 0 then s[i] == -old(s[i]) else s[i] == old(s[i])
ensures s.Length == old(s).Length
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant forall k :: 0 <= k < i ==> (old(s[k]) < 0 && s[k] == -old(s[k])) || (old(s[k]) >= 0 && s[k] == old(s[k]))
    invariant s.Length == old(s).Length
    invariant forall k :: i <= k < s.Length ==> s[k] == old(s[k])
  {
    if s[i] < 0 {
      s[i] := -s[i];
    }
    i := i + 1;
  }
}
// </vc-code>

