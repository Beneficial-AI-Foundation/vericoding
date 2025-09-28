use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>
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
    proof {
        let mut min_sublist = s@[0];
        let mut min_len: nat = min_sublist.len();

        let mut i: nat = 1nat;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                min_sublist.len() == min_len,
                forall |j: nat| 0 <= j < i ==> s@[j].len() >= min_sublist.len(),
        {
            if s@[i].len() < min_len {
                min_sublist = s@[i];
                min_len = s@[i].len();
            }
            i = i + 1;
        }

        proof {
            assert(s.contains(min_sublist));
            assert(forall |sublist: Seq<int>| #[trigger] s.contains(sublist) ==> min_sublist.len() <= sublist.len());
        }
        return min_sublist;
    }
}
// </vc-code>

fn main() {
}

}