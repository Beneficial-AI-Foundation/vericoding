use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier(external_body)]
#[allow(unused_mut)]
#[allow(unused_variables)]
#[allow(dead_code)]
pub fn set_from_seq<T>(s: Seq<T>) -> Set<T>
    ensures forall|t: T| s.contains(t) <==> Set::<T>::empty().union(s.to_set()).contains(t)
{
    let mut set: Set<T> = Set::empty();
    let mut i: nat = 0_nat;
    while i < s.len()
        invariant
            0 <= i,
            i <= s.len(),
            forall|t: T| (exists|j: nat| j < i && #[trigger] s.index(j as int) == t) <==> set.contains(t),
    {
        set = set.insert(s.index(i as int));
        i = i + 1;
    }
    set
}
// </vc-helpers>

// <vc-spec>
fn filter(a: Seq<char>, b: Set<char>) -> (c: Set<char>)
    ensures forall|x: char| a.contains(x) && b.contains(x) <==> c.contains(x)
// </vc-spec>
// <vc-code>
{
    let a_set = set_from_seq(a);
    a_set.intersect(b)
}
// </vc-code>

fn main() {
}

}