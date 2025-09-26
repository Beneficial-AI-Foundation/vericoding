// <vc-preamble>
method toMultiset(s: string) returns (mset: multiset<char>)
    ensures multiset(s) == mset
{
  assume{:axiom} false;
}

method msetEqual(s: multiset<char>, t: multiset<char>) returns (equal: bool)
    ensures s == t <==> equal
{
  assume{:axiom} false;
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method isAnagram(s: string, t: string) returns (equal: bool)
    ensures (multiset(s) == multiset(t)) == equal
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
