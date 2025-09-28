use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn min_length_sublist(s: Seq<Seq<int>>) -> (min_sublist: Seq<int>)
    requires 
        s.len() > 0,
    ensures 
        s.contains(min_sublist),
        forall |sublist: Seq<int>| s.contains(sublist) ==> min_sublist.len() <= sublist.len(),
// </vc-spec>
// <vc-code>
{
    let mut i: nat = 1;
    let mut best: Seq<int> = s.index(0);
    while i < s.len()
        invariant i <= s.len();
        invariant s.contains(best);
        invariant forall |j: nat| #[trigger] j < i ==> best.len() <= s.index(j).len();
    {
        let cur = s.index(i);
        if cur.len() < best.len() {
            best = cur;
        }
        i = i + 1;
    }
    proof {
        assert(s.contains(best));
        assert(forall |sub: Seq<int>| s.contains(sub) ==> best.len() <= sub.len());
    }
    best
}
// </vc-code>

fn main() {
}

}