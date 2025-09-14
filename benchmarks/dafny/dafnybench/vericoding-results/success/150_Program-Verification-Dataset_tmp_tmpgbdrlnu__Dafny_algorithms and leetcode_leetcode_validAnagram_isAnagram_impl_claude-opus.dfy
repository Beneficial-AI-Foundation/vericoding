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

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method isAnagram(s: string, t: string) returns (equal: bool)
    ensures (multiset(s) == multiset(t)) == equal
// </vc-spec>
// <vc-code>
{
  var msetS := toMultiset(s);
  var msetT := toMultiset(t);
  equal := msetEqual(msetS, msetT);
}
// </vc-code>

