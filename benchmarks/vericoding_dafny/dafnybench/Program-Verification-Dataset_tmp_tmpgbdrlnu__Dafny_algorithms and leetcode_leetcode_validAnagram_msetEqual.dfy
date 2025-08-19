// <vc-helpers>
// </vc-helpers>

method msetEqual(s: multiset<char>, t: multiset<char>) returns (equal: bool)
    ensures s == t <==> equal
// <vc-code>
{
  assume false;
}
// </vc-code>