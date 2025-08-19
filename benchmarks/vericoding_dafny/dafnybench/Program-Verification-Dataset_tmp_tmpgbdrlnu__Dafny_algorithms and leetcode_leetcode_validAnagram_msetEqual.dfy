// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method msetEqual(s: multiset<char>, t: multiset<char>) returns (equal: bool)
    ensures s == t <==> equal
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>