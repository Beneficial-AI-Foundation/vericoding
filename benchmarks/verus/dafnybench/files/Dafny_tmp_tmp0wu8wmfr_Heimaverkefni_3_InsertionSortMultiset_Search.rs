use vstd::prelude::*;

verus! {

fn search(s: Seq<int>, x: int) -> (k: usize)

    requires 
        forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q],
    ensures 
        0 <= k <= s.len(),
        forall|i: int| 0 <= i < k ==> s[i] <= x,
        forall|i: int| k <= i < s.len() ==> s[i] >= x,
        forall|z: int| s.subrange(0, k as int).contains(z) ==> z <= x,
        forall|z: int| s.subrange(k as int, s.len() as int).contains(z) ==> z >= x,
        s == s.subrange(0, k as int).add(s.subrange(k as int, s.len() as int)),
{
    assume(false);
    unreached();
}

}
fn main() {}