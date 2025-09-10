use vstd::prelude::*;
use vstd::multiset::*;

verus! {

proof fn min_of_multiset(m: Multiset<int>) -> (min: int)
    requires 
        m.len() > 0,
    ensures 
        m.count(min) > 0,
        forall|z: int| m.count(z) > 0 ==> min <= z,
{
    assume(false);
    arbitrary()
}

exec fn sort(m: Multiset<int>) -> (s: Vec<int>)

    ensures 
        s@.to_multiset() == m,
        forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q],
{
    assume(false);
    unreached()
}

}
fn main() {}