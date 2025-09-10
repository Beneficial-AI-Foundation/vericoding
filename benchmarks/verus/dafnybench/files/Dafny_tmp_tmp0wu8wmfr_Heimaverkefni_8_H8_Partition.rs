use vstd::prelude::*;
use vstd::multiset::Multiset;

verus! {

fn partition(Ghost(m): Ghost<Multiset<int>>) -> (res: (Ghost<Multiset<int>>, Ghost<int>, Ghost<Multiset<int>>))
    requires m.len() > 0
    ensures 
        ({
            let (Ghost(pre), Ghost(p), Ghost(post)) = res;
            &&& m.contains(p)
            &&& m == pre.add(Multiset::singleton(p)).add(post)
            &&& forall|z: int| pre.contains(z) ==> z <= p
            &&& forall|z: int| post.contains(z) ==> z >= p
        })
{
    assume(false);
    unreached();
}

}
fn main() {}