// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method AbsIt(s: array<int>) modifies s;
//requires 
ensures forall x :: 0 <= x < s.Length ==> old(s[x]) < 0 ==> s[x] == -old(s[x])
ensures forall x :: 0 <= x < s.Length ==> old(s[x]) >= 0 ==> s[x] == old(s[x])
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>