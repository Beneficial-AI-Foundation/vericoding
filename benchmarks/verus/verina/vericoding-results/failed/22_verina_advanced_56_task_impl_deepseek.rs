// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_val(val: i32, xs: Seq<i32>) -> nat 
    decreases xs.len()
{
    if xs.len() == 0 {
        0
    } else {
        let rest = count_val(val, xs.drop_first());
        if xs[0] == val { rest + 1 } else { rest }
    }
}

spec fn is_subsequence(xs: Seq<i32>, ys: Seq<i32>) -> bool 
    decreases xs.len() + ys.len()
{
    if xs.len() == 0 {
        true
    } else if ys.len() == 0 {
        false
    } else {
        if xs[0] == ys[0] {
            is_subsequence(xs.drop_first(), ys.drop_first())
        } else {
            is_subsequence(xs, ys.drop_first())
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helpers modified by LLM (iteration 5): Fixed type conversion issues and added proper invariants */
fn swap_vec_elements(vec: &mut Vec<i32>, i: usize, j: usize)
    requires
        0 <= i < vec.len(),
        0 <= j < vec.len()
    ensures
        vec@ == old(vec)@.update(i, old(vec)@[j]).update(j, old(vec)@[i])
{
    let temp = vec[i];
    vec[i] = vec[j];
    vec[j] = temp;
}

proof fn lemma_count_val_filter_nonzero(xs: Seq<i32>) 
    ensures 
        count_val(0, xs.filter(|x: i32| x != 0)) == 0,
    decreases xs.len()
{
    if xs.len() == 0 {
    } else {
        lemma_count_val_filter_nonzero(xs.drop_first());
    }
}

proof fn lemma_is_subsequence_filter_nonzero(xs: Seq<i32>) 
    ensures 
        is_subsequence(xs.filter(|x: i32| x != 0), xs),
    decreases xs.len()
{
    if xs.len() == 0 {
    } else {
        lemma_is_subsequence_filter_nonzero(xs.drop_first());
    }
}

proof fn lemma_count_val_preserved(xs: Seq<i32>, ys: Seq<i32>) 
    requires 
        xs.len() == ys.len(),
        count_val(0, xs) == count_val(0, ys),
    ensures 
        count_val(0, xs.filter(|x: i32| x != 0)) == count_val(0, ys.filter(|x: i32| x != 0)),
    decreases xs.len()
{
    if xs.len() == 0 {
    } else {
        lemma_count_val_preserved(xs.drop_first(), ys.drop_first());
    }
}

spec fn seq_range_eq(xs: Seq<i32>, ys: Seq<i32>, end: int) -> bool {
    xs.subrange(0, end) == ys.subrange(0, end)
}
// </vc-helpers>

// <vc-spec>
fn move_zeroes(xs: Vec<i32>) -> (result: Vec<i32>)
    ensures

        is_subsequence(xs@.filter(|x: i32| x != 0), result@),

        forall|i: int| 0 <= i < result.len() && result[i] != 0 ==> 
            forall|j: int| i < j < result.len() ==> result[j] != 0,

        xs.len() == result.len(),

        count_val(0, xs@) == count_val(0, result@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type conversion issues and loop invariants */
{
    let mut result = xs.clone();
    let mut i: usize = 0;
    let mut j: usize = 0;
    
    while i < result.len()
        invariant
            0 <= i <= result.len(),
            0 <= j <= result.len(),
            forall|k: int| 0 <= k < j as int ==> result[k as usize] != 0,
            forall|k: int| j as int <= k < i as int ==> result[k as usize] == 0,
            seq_range_eq(xs@, result@, i as int),
            count_val(0, xs@) == count_val(0, result@),
        decreases result.len() - i
    {
        if result[i] != 0 {
            swap_vec_elements(&mut result, i, j);
            j += 1;
        }
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}