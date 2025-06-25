pub fn toMultiset(s: &str) -> (mset: Multiset<char>)
    ensures(Multiset::from_seq(s@) == mset)
{
}