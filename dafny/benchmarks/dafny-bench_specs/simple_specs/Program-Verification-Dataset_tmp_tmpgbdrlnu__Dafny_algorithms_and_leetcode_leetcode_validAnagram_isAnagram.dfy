//ATOM

method toMultiset(s: string) returns (mset: multiset<char>)
  ensures multiset(s) == mset
{
  mset := multiset{};
  assume multiset(s) ==> mset;
  return mset;
}


//ATOM

method msetEqual(s: multiset<char>, t: multiset<char>) returns (equal: bool)
  ensures s == t <==> equal
{
  equal := false;
  assume s ==> t <==> equal;
  return equal;
}


// SPEC

method isAnagram(s: string, t: string) returns (equal: bool)
  ensures (multiset(s) == multiset(t)) == equal
{
}
