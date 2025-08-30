
// SPEC 

method toMultiset(s: string) returns (mset: multiset<char>)
    ensures multiset(s) == mset
{
}


// SPEC 

method msetEqual(s: multiset<char>, t: multiset<char>) returns (equal: bool)
    ensures s == t <==> equal
{
}


// SPEC 

method isAnagram(s: string, t: string) returns (equal: bool)
    ensures (multiset(s) == multiset(t)) == equal
{
}


