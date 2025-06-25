pub fn toMultiset(s: &str) -> Multiset<char>
    ensures(multiset(s.view()) == result)
{
}

pub fn msetEqual(s: Multiset<char>, t: Multiset<char>) -> bool
    ensures(s == t <==> result)
{
}

pub fn isAnagram(s: &str, t: &str) -> bool
    ensures((multiset(s.view()) == multiset(t.view())) == result)
{
}