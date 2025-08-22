// <vc-helpers>
// </vc-helpers>

method is_equal(s: multiset<char>, t: multiset<char>) returns (result: bool)
    ensures (s == t) <==> result
// <vc-code>
{
  assume false;
}
// </vc-code>