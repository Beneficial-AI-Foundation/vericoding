// <vc-preamble>

function CharSet(s: string): set<char>
{
    set c | c in s
}
// </vc-preamble>

// <vc-helpers>
lemma Helpers_Sanity() ensures true {
}

// </vc-helpers>

// <vc-spec>
method same_chars(s0: string, s1: string) returns (result: bool)
    ensures result == (CharSet(s0) == CharSet(s1))
// </vc-spec>
// <vc-code>
{
  var set0 := CharSet(s0);
  var set1 := CharSet(s1);
  result := set0 == set1;
}
// </vc-code>
