// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(xs: Seq<i32>, target: i32) -> nat {
    xs.filter(|x: i32| x == target).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): nonnegativity of count_occurrences */
proof fn count_nonneg(xs: Seq<i32>, x: i32) ensures count_occurrences(xs, x) >= 0 { proof { assert(count_occurrences(xs, x) >= 0); } }

/* helper modified by LLM (iteration 5): existence of index witnessing sequence containment */
proof fn contains_index(xs: Seq<i32>, v: i32) requires xs@.contains(v) ensures exists|idx: int| 0 <= idx < xs.len() && xs@[idx] == v { proof { assert(xs@.contains(v)); assert(exists|i: int| 0 <= i < xs.len() && xs@[i] == v); } }
// </vc-helpers>

// <vc-spec>
fn most_frequent(xs: Vec<i32>) -> (result: i32)
    requires xs.len() > 0,
    ensures
        xs@.contains(result),
        forall|x: i32| xs@.contains(x) ==> count_occurrences(xs@, x) <= count_occurrences(xs@, result),
        exists|first_idx: int| 
            0 <= first_idx < xs.len() && 
            xs[first_idx] == result && 
            count_occurrences(xs@, result) == count_occurrences(xs@, xs[first_idx]) &&
            forall|i: int| 0 <= i < first_idx ==> count_occurrences(xs@, xs[i]) < count_occurrences(xs@, result),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): scan vector and maintain most frequent element with first-index tie-breaker */
    let n: int = xs.len() as int;
    let mut result: i32 = xs[0];
    let mut result_idx: int = 0;
    let mut i: int = 1;
    while i < n
        invariant 0 <= i && i <= n,
        invariant 0 <= result_idx && result_idx < n,
        invariant result == xs[result_idx],
        invariant xs@.contains(result),
        invariant forall|j: int| 0 <= j < i ==> count_occurrences(xs@, xs@[j]) <= count_occurrences(xs@, result),
        invariant forall|j: int| 0 <= j < result_idx ==> count_occurrences(xs@, xs@[j]) < count_occurrences(xs@, result),
        decreases n - i
    {
        let cur: i32 = xs[i];
        let cur_count: nat = count_occurrences(xs@, cur);
        let res_count: nat = count_occurrences(xs@, result);
        if cur_count > res_count {
            result = cur;
            result_idx = i;
            proof {
                assert(cur_count > res_count);
                assert(count_occurrences(xs@, xs@[i]) == cur_count);
                assert(forall|j: int| 0 <= j < i ==> count_occurrences(xs@, xs@[j]) <= res_count);
                assert(forall|j: int| 0 <= j < i ==> count_occurrences(xs@, xs@[j]) < cur_count);
                assert(forall|j: int| 0 <= j < i + 1 ==> count_occurrences(xs@, xs@[j]) <= cur_count);
                assert(forall|j: int| 0 <= j < result_idx ==> count_occurrences(xs@, xs@[j]) < count_occurrences(xs@, result));
                assert(result == xs[result_idx]);
                assert(xs@.contains(result));
            }
        } else {
            proof {
                assert(cur_count <= res_count);
                assert(count_occurrences(xs@, xs@[i]) <= res_count);
                assert(forall|j: int| 0 <= j < i + 1 ==> count_occurrences(xs@, xs@[j]) <= res_count);
                assert(result == xs[result_idx]);
                assert(xs@.contains(result));
            }
        }
        i = i + 1;
    }
    proof {
        assert(0 <= result_idx && result_idx < n);
        assert(xs[result_idx] == result);
        assert(forall|j: int| 0 <= j < result_idx ==> count_occurrences(xs@, xs@[j]) < count_occurrences(xs@, result));
        assert(forall|x: i32| xs@.contains(x) ==> count_occurrences(xs@, x) <= count_occurrences(xs@, result));
    }
    result
}
// </vc-code>

}
fn main() {}