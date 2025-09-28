use vstd::prelude::*;

verus! {

spec fn is_peek(v: &Vec<i32>, i: int) -> bool
    recommends 0 <= i < v.len()
{
    forall|k: int| 0 <= k < i ==> v[i] >= v[k]
}

spec fn peek_sum(v: &Vec<i32>, i: int) -> int
    recommends 0 <= i <= v.len()
    decreases i when 0 <= i <= v.len()
{
    if i == 0 {
        0
    } else {
        if is_peek(v, i - 1) {
            v[i - 1] + peek_sum(v, i - 1)
        } else {
            peek_sum(v, i - 1)
        }
    }
}

// <vc-helpers>
// Added a small helper lemma to extract a witness from an existence of equality
// and produce an existence of a strict inequality when combined with a > fact.
lemma fn exists_gt_from_eq_and_gt(v: &Vec<i32>, i: int, cur_max: i32)
    requires 0 <= i && i <= v.len()
    requires exists|j: int| 0 <= j && j < i && cur_max == v@[j]
    requires cur_max > v@[i]
    ensures exists|j: int| 0 <= j && j < i && v@[j] > v@[i]
{
    proof {
        let j0: int = choose |j: int| 0 <= j && j < i && cur_max == v@[j];
        assert(v@[j0] == cur_max);
        assert(v@[j0] > v@[i]);
        assert(0 <= j0 && j0 < i && v@[j0] > v@[i]);
    }
}
// </vc-helpers>

// <vc-spec>
fn m_peek_sum(v: &Vec<i32>) -> (sum: i32)
    requires v.len() > 0
    ensures sum == peek_sum(v, v.len() as int)
    //Implement and verify an O(v.len()) algorithm to solve this problem
// </vc-spec>
// <vc-code>
{
    let n = v.len() as int;
    // Initialize processing with first element handled
    let mut i: int = 1;
    let mut sum: i32 = if is_peek(v, 0) { v[0] } else { 0 };
    let mut cur_max: i32 = v[0];

    proof {
        // relate runtime and spec indexing for index 0
        assert(v[0] == v@[0]);
        // show sum == peek_sum(v, 1)
        if is_peek(v, 0) {
            assert(peek_sum(v, 1) == (v@[0] as int) + peek_sum(v, 0));
        } else {
            assert(peek_sum(v, 1) == peek_sum(v, 0));
        }
        assert((sum as int) == peek_sum(v, 1));
        // cur_max corresponds to some prior element and is an upper bound
        assert(forall|k: int| 0 <= k && k < 1 ==> cur_max >= v@[k]);
        assert(exists|k: int| 0 <= k && k < 1 && cur_max == v@[k]);
    }

    while i < n
        invariant 0 <= i && i <= n
        invariant (sum as int) == peek_sum(v, i)
        invariant forall|k: int| 0 <= k && k < i ==> cur_max >= v@[k]
        invariant exists|k: int| 0 <= k && k < i && cur_max == v@[k]
        decreases n - i
    {
        let val: i32 = v[i as usize];

        if val >= cur_max {
            sum = sum + val;
            cur_max = val;
            proof {
                // relate runtime and spec indexing
                assert(val == v@[i]);
                // since cur_max >= all previous and val >= cur_max, val >= all previous
                assert(forall|k: int| 0 <= k && k < i ==> cur_max >= v@[k]);
                assert(val >= cur_max);
                // combine to get val >= all previous
                assert(forall|k: int| 0 <= k && k < i ==> val >= v@[k]);
                assert(is_peek(v, i));
                // use definition of peek_sum for the (i+1) case
                assert(peek_sum(v, i + 1) == (v@[i] as int) + peek_sum(v, i));
                assert((sum as int) == peek_sum(v, i + 1));
                // cur_max is now v@[i], so existence holds for new i+1
                assert(0 <= i && i < i + 1 && cur_max == v@[i]);
                assert(exists|k: int| 0 <= k && k < i + 1 && cur_max == v@[k]);
                // cur_max >= all previous still holds
                assert(forall|k: int| 0 <= k && k < i + 1 ==> cur_max >= v@[k]);
            }
        } else {
            proof {
                assert(val == v@[i]);
                // extract witness j0 for previous existence cur_max == v@[j0]
                let j0: int = choose |j: int| 0 <= j && j < i && cur_max == v@[j];
                assert(0 <= j0 && j0 < i);
                assert(v@[j0] == cur_max);
                assert(cur_max > v@[i]);
                // from equality and > produce existence of j with v[j] > v[i]
                assert(v@[j0] > v@[i]);
                assert(0 <= j0 && j0 < i && v@[j0] > v@[i]);
                assert(exists|j: int| 0 <= j && j < i && v@[j] > v@[i]);
                assert(!is_peek(v, i));
                // use definition of peek_sum for the (i+1) case
                assert(peek_sum(v, i + 1) == peek_sum(v, i));
                assert((sum as int) == peek_sum(v, i + 1));
                // existence invariant preserved (same j0 works for i+1)
                assert(0 <= j0 && j0 < i + 1 && cur_max == v@[j0]);
                assert(exists|k: int| 0 <= k && k < i + 1 && cur_max == v@[k]);
                // cur_max >= all previous including v@[i]
                // for k < i use the invariant, for k == i use cur_max > v@[i]
                assert(forall|k: int| 0 <= k && k < i + 1 ==> cur_max >= v@[k]);
            }
        }

        i = i + 1;
    }

    sum
}
// </vc-code>

fn main() {}

}