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
  var mset_s := toMultiset(s);
  var mset_t := toMultiset(t);
  equal := msetEqual(mset_s, mset_t);
}
// </vc-code>

