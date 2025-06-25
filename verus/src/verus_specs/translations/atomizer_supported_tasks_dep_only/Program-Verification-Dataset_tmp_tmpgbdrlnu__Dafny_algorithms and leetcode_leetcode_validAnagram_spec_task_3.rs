pub fn toMultiset(s: &str) -> Multiset<char>
    ensures(result == s@.to_multiset())
{
}

pub fn msetEqual(s: Multiset<char>, t: Multiset<char>) -> bool
    ensures((s == t) <==> result)
{
}

pub fn isAnagram(s: &str, t: &str) -> bool
    ensures((s@.to_multiset() == t@.to_multiset()) == result)
{
}