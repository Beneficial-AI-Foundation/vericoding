//IMPL toMultiset
method toMultiset(s: string) returns (mset: multiset<char>)
    ensures multiset(s) == mset
{
    mset := multiset(s);
}

//IMPL msetEqual
method msetEqual(s: multiset<char>, t: multiset<char>) returns (equal: bool)
    ensures s == t <==> equal
{
    equal := s == t;
}

//IMPL isAnagram
method isAnagram(s: string, t: string) returns (equal: bool)
    ensures (multiset(s) == multiset(t)) == equal
{
    equal := multiset(s) == multiset(t);
}