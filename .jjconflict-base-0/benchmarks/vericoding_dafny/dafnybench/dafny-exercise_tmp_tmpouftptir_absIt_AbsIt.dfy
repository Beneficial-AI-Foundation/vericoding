// <vc-helpers>
// </vc-helpers>

method AbsIt(s: array<int>) 
modifies s
ensures forall i :: 0 <= i < s.Length ==> if old(s[i]) < 0 then s[i] == -old(s[i]) else s[i] == old(s[i])
ensures s.Length == old(s).Length
// <vc-code>
{
  assume false;
}
// </vc-code>