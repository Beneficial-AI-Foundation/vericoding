//IMPL 

method toMultiset(s: string) returns (mset: multiset<char>)
    ensures multiset(s) == mset
{
    mset := multiset(s);
}


//ATOM_PLACEHOLDER_msetEqual

//ATOM_PLACEHOLDER_isAnagram