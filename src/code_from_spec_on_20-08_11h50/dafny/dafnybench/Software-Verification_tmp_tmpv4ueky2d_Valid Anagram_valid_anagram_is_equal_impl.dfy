method is_equal(s: multiset<char>, t: multiset<char>) returns (result: bool)
    ensures (s == t) <==> result
// </vc-spec>
// <vc-code>
{
  result := s == t;
}
// </vc-code>