use vstd::prelude::*;

verus! {

// <vc-helpers>
use vstd::seq::Seq;

// Helper function to find the minimum of a sequence of nats
proof fn min_seq_nat(s: Seq<nat>) -> nat
    requires
        s.len() > 0,
    ensures
        s.contains(min_seq_nat(s)),
        forall |x: nat| s.contains(x) ==> min_seq_nat(s) <= x,
{
    if s.len() == 1 {
        s[0]
    } else {
        let first = s[0];
        let rest_min = min_seq_nat(s.subsequence(1, s.len() as int));
        if first <= rest_min {
            first
        } else {
            rest_min
        }
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn smallest_list_length(lists: Vec<Vec<i32>>) -> (result: usize)
    // pre-conditions-start
    requires
        lists.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        exists|i: int| #![auto] 0 <= i < lists.len() && result == lists[i].len(),
        forall|i: int| #![auto] 0 <= i < lists.len() ==> result <= lists[i].len(),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut smallest_len: usize = lists[0].len();
    let mut i: usize = 1;

    let list_lengths_seq_val = Seq::new(lists.len(), |j: int| {
        #[verifier::spec] let len_as_nat: nat = lists[j as usize].len() as nat;
        len_as_nat
    });

    assert(smallest_len == list_lengths_seq_val.index(0) as usize);

    while i < lists.len()
        invariant
            0 < i,
            i <= lists.len(),
            smallest_len == min_seq_nat(list_lengths_seq_val.subsequence(0, i as int)) as usize,
    {
        if lists[i].len() < smallest_len {
            smallest_len = lists[i].len();
        }
        i = i + 1;
    }

    assert(smallest_len == min_seq_nat(list_lengths_seq_val) as usize);
    smallest_len
    // impl-end
}
// </vc-code>

fn main() {}
}