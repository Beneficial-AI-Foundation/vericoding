// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: Seq<int>) -> bool {
    a.len() > 0
}

spec fn is_sorted(x: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < x.len() ==> x[i] <= x[j]
}

spec fn thanos_sort(x: Seq<int>) -> int
    recommends x.len() > 0
    decreases x.len()
{
    let len = x.len() as int;
    if is_sorted(x) {
        len
    } else {
        let first_half = x.subrange(0, len / 2);
        let second_half = x.subrange(len / 2, len);
        let left_result = thanos_sort(first_half);
        let right_result = thanos_sort(second_half);
        if left_result > right_result { left_result } else { right_result }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [used correct vstd lemma for sortedness] */
fn is_slice_sorted(x: &[i8]) -> (result: bool)
    ensures result == is_sorted(x@.map(|i, v| v as int))
{
    let ghost s_int = x@.map(|_, v| v as int);
    let mut i: usize = 0;
    while i + 1 < x.len()
        invariant
            forall|k: int| 0 <= k < i as int ==> s_int[k] <= s_int[k + 1],
    {
        if x[i] > x[i + 1] {
            return false;
        }
        i = i + 1;
    }

    proof {
        vstd::seq_lib::lemma_is_sorted_by_forall_adjacent(s_int);
    }
    
    true
}

/* helper modified by LLM (iteration 5): [no logical change from previous turn] */
fn thanos_sort_recursive(x: &[i8]) -> (result: usize)
    requires
        x.len() > 0,
    ensures
        result as int == thanos_sort(x@.map(|i, v| v as int)),
        1 <= result <= x.len(),
    decreases x.len()
{
    if is_slice_sorted(x) {
        return x.len();
    }
    
    proof {
        assert(!is_sorted(x@.map(|i,v|v as int)));
        assert(x.len() >= 2);
    }

    let mid = x.len() / 2;
    assert(mid > 0);
    let (first_half, second_half) = x.split_at(mid);
    assert(first_half.len() > 0);
    assert(second_half.len() > 0);

    let left_result = thanos_sort_recursive(first_half);
    let right_result = thanos_sort_recursive(second_half);

    if left_result > right_result {
        left_result
    } else {
        right_result
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>) -> (result: usize)
    requires 
        valid_input(a@.map(|i, x| x as int)),
    ensures 
        result as int == thanos_sort(a@.map(|i, x| x as int)),
        1 <= result <= a.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [no logical change, only comment updated] */
    thanos_sort_recursive(a.as_slice())
}
// </vc-code>


}

fn main() {}