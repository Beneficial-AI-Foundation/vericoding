//ATOM_PLACEHOLDER_toMultiset

//IMPL 
method msetEqual(s: multiset<char>, t: multiset<char>) returns (equal: bool)
    ensures s == t <==> equal
{
    equal := s == t;
}

//ATOM_PLACEHOLDER_isAnagram