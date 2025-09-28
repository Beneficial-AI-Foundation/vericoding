use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn vec_clone_preserves_seq<T>(v: &Vec<T>) -> Vec<T>
    ensures result@ == v@,
            result.len() == v.len()
{
    let r = v.clone();
    proof {
        assert(r.len() == v.len());
        assert(r@ == v@);
    }
    r
}
// </vc-helpers>

// <vc-spec>
fn max_length_list(lists: &Vec<Vec<int>>) -> (max_list: Vec<int>)
    requires lists.len() > 0
    ensures forall|i: int| 0 <= i < lists.len() ==> lists[i].len() <= max_list.len(),
            exists|i: int| 0 <= i < lists.len() && max_list@ == lists[i]@
// </vc-spec>
// <vc-code>
{
    let n = lists.len();
    let mut best: nat = 0;
    let mut i: nat = 1;
    while i < n
        invariant i <= n;
        invariant best < n;
        invariant forall |j: nat| j < i ==> lists.index(j).len() <= lists.index(best).len();
        decreases n - i;
    {
        if lists.index(i).len() > lists.index(best).len() {
            best = i;
        }
        i = i + 1;
    }
    let max_list = vec_clone_preserves_seq(lists.index(best));
    proof {
        // From the loop invariant at termination (i == n)
        assert(forall |j: nat| j < n ==> lists.index(j).len() <= lists.index(best).len());
        // Convert the above to an int-indexed property to satisfy the spec's quantifier
        assert(forall |ii: int| 0 <= ii && ii < (n as int) ==> lists.index(ii as nat).len() <= lists.index(best).len());
        // clone (via helper) preserves length and sequence representation
        assert(max_list.len() == lists.index(best).len());
        assert(max_list@ == lists.index(best)@);
        // Now establish the ensures clauses
        assert(forall |ii: int| 0 <= ii && ii < (lists.len() as int) ==> lists.index(ii as nat).len() <= max_list.len());
        assert(0 <= (best as int) && (best as int) < (lists.len() as int));
        // Provide the existential witness for the second ensures clause
        assert(exists |ii: int| 0 <= ii && ii < (lists.len() as int) && max_list@ == lists.index(ii as nat)@);
        // can witness best
        assert(exists |ii: int| ii == (best as int) && 0 <= ii && ii < (lists.len() as int) && max_list@ == lists.index(ii as nat)@);
    }
    max_list
}
// </vc-code>

fn main() {}

}