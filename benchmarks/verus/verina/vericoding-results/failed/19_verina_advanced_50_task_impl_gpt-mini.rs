// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(v: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> #[trigger] v[i] <= #[trigger] v[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): totalized prefix_multiset with explicit termination */
use vstd::multiset::Multiset;

spec fn prefix_multiset(a: &Vec<nat>, k: int) -> Multiset<nat>
    requires
        k >= 0,
    decreases
        k
{
    if k == 0 {
        Multiset::empty()
    } else if k >= a.len() as int {
        a@.to_multiset()
    } else {
        prefix_multiset(a, k - 1).add(Multiset::singleton(a@[k - 1]))
    }
}
// </vc-helpers>

// <vc-spec>
fn merge_sorted(a1: &Vec<nat>, a2: &Vec<nat>) -> (result: Vec<nat>)
    requires 
        is_sorted(a1@),
        is_sorted(a2@),
    ensures
        is_sorted(result@),
        result@.to_multiset() == a1@.to_multiset().add(a2@.to_multiset()),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): merge two sorted vectors into result maintaining invariants and proving multisets */
    let mut result: Vec<nat> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;

    while i < a1.len() || j < a2.len()
        invariant
            0 <= i as int,
            i as int <= a1.len() as int,
            0 <= j as int,
            j as int <= a2.len() as int,
            result@.len() == (i as int + j as int),
            result@.to_multiset() == prefix_multiset(a1, i as int).add(prefix_multiset(a2, j as int)),
            is_sorted(result@),
            (result@.len() > 0 ==> forall|k: int| i as int <= k < a1.len() as int ==> a1@[k] >= result@[result@.len()-1]),
            (result@.len() > 0 ==> forall|k: int| j as int <= k < a2.len() as int ==> a2@[k] >= result@[result@.len()-1]),
        decreases (a1.len() as int + a2.len() as int) - (i as int + j as int)
    {
        if i < a1.len() && (j >= a2.len() || a1[i] <= a2[j]) {
            let old_i = i;
            let x: nat = a1[old_i];
            result.push(x);
            i += 1;
            proof {
                // use preconditions
                assert(is_sorted(a1@));
                assert(is_sorted(a2@));

                // update multiset: prefix_multiset(a1, old_i+1) = prefix_multiset(a1, old_i) + {a1[old_i]}
                assert(prefix_multiset(a1, old_i as int + 1) == prefix_multiset(a1, old_i as int).add(Multiset::singleton(a1@[old_i as int])));
                // new result multiset equals updated prefixes
                assert(result@.to_multiset() == prefix_multiset(a1, old_i as int + 1).add(prefix_multiset(a2, j as int)));
                // length relation
                assert(result@.len() == i as int + j as int);

                // show new last element properties
                // a1 elements after old_i are >= a1[old_i] because a1 is sorted
                assert(forall|k: int| old_i as int + 1 <= k < a1.len() as int ==> a1@[k] >= a1@[old_i as int]));
                // show a2 elements from j are >= a1[old_i]
                if j < a2.len() {
                    // branch condition ensured a1[old_i] <= a2[j]
                    assert(a1@[old_i as int] <= a2@[j as int]);
                    assert(forall|k: int| j as int <= k < a2.len() as int ==> a2@[k] >= a2@[j as int]));
                    assert(forall|k: int| j as int <= k < a2.len() as int ==> a2@[k] >= a1@[old_i as int]));
                }

                // maintain sortedness: previous result was sorted and new last >= previous last
                assert(is_sorted(result@));
            }
        } else {
            let old_j = j;
            let x: nat = a2[old_j];
            result.push(x);
            j += 1;
            proof {
                // use preconditions
                assert(is_sorted(a1@));
                assert(is_sorted(a2@));

                // update multiset
                assert(prefix_multiset(a2, old_j as int + 1) == prefix_multiset(a2, old_j as int).add(Multiset::singleton(a2@[old_j as int])));
                assert(result@.to_multiset() == prefix_multiset(a1, i as int).add(prefix_multiset(a2, old_j as int + 1)));
                // length relation
                assert(result@.len() == i as int + j as int);

                // show new last element properties
                // a1 elements from i are >= a2[old_j]
                if i < a1.len() {
                    // branch condition in this case ensures a2[old_j] < a1[i] or j < a2.len() was chosen; but sortedness of a1 gives bounds
                    assert(forall|k: int| i as int <= k < a1.len() as int ==> a1@[k] >= a1@[i as int]));
                }
                // a2 elements after old_j are >= a2[old_j]
                assert(forall|k: int| old_j as int + 1 <= k < a2.len() as int ==> a2@[k] >= a2@[old_j as int]));

                // maintain sortedness
                assert(is_sorted(result@));
            }
        }
    }

    result
}

// </vc-code>

}
fn main() {}