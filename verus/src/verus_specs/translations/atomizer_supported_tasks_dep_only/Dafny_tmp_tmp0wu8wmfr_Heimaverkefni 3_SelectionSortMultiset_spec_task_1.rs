// Hjálparfall sem finnur minnsta gildi í poka
pub fn min_of_multiset(m: Multiset<int>) -> (min: int)
    requires(m != Multiset::empty())
    ensures(m.count(min) > 0)
    ensures(forall|z: int| m.count(z) > 0 ==> min <= z)
{
}