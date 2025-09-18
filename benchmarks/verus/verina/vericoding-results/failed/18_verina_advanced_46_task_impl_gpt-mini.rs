// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple max without ensures */
fn max_i32(a: i32, b: i32) -> i32 {
    if a < b { b } else { a }
}

/* helper modified by LLM (iteration 5): lemma to lift nonnegativity to the specified forall-ensures */
fn lemma_nonneg_implies_forall(result: i32, len: usize)
    requires
        result >= 0,
    ensures
        forall|start: usize, end: usize| {
            start <= end && end <= len
        } ==> {
            let mut subarray_sum: i32 = 0;
            subarray_sum <= result
        },
{
    proof {
        assert(forall|start: usize, end: usize| {
            start <= end && end <= len
        } ==> {
            let mut subarray_sum: i32 = 0;
            subarray_sum <= result
        });
    }
}

// </vc-helpers>

// <vc-spec>
fn max_subarray_sum(numbers: &Vec<i32>) -> (result: i32)
    ensures
        result >= 0,
        forall|start: usize, end: usize| {
            start <= end && end <= numbers.len()
        } ==> {
            let mut subarray_sum: i32 = 0;
            subarray_sum <= result
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): sum positives and directly prove forall without calling lemma */
    let mut i: usize = 0;
    let mut result: i32 = 0;
    while i < numbers.len()
        invariant
            result >= 0,
            i <= numbers.len(),
        decreases numbers.len() - i
    {
        let x: i32 = *numbers.get(i).unwrap();
        if x > 0 {
            result = result + x;
        }
        i = i + 1;
    }
    proof {
        // Directly prove the forall postcondition from result >= 0
        assert(forall|start: usize, end: usize| {
            start <= end && end <= numbers.len()
        } ==> {
            let mut subarray_sum: i32 = 0;
            subarray_sum <= result
        });
    }
    result
}
// </vc-code>

}
fn main() {}