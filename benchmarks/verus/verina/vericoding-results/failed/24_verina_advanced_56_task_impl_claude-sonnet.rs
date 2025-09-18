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
/* helper modified by LLM (iteration 5): fixed nat literal comparisons and sequence indexing syntax */
fn lemma_count_val_preservation(val: i32, xs: Seq<i32>, result: Seq<i32>)
    requires xs.len() == result.len(),
             forall|i: int| 0 <= i < xs.len() ==> (xs[i] == val <==> result[i] == val)
    ensures count_val(val, xs) == count_val(val, result)
    decreases xs.len()
{
    if xs.len() == 0nat {
    } else {
        lemma_count_val_preservation(val, xs.drop_first(), result.drop_first());
    }
}

fn lemma_filter_subsequence_trans(xs: Seq<i32>, ys: Seq<i32>, zs: Seq<i32>)
    requires is_subsequence(xs, ys), is_subsequence(ys, zs)
    ensures is_subsequence(xs, zs)
    decreases xs.len() + ys.len() + zs.len()
{
    if xs.len() == 0nat {
    } else if ys.len() == 0nat {
    } else if zs.len() == 0nat {
    } else {
        if xs@[0] == ys@[0] {
            if ys@[0] == zs@[0] {
                lemma_filter_subsequence_trans(xs.drop_first(), ys.drop_first(), zs.drop_first());
            } else {
                lemma_filter_subsequence_trans(xs, ys, zs.drop_first());
            }
        } else {
            if ys@[0] == zs@[0] {
                lemma_filter_subsequence_trans(xs, ys.drop_first(), zs.drop_first());
            } else {
                lemma_filter_subsequence_trans(xs, ys, zs.drop_first());
            }
        }
    }
}

fn lemma_count_val_append(val: i32, xs: Seq<i32>, ys: Seq<i32>)
    ensures count_val(val, xs + ys) == count_val(val, xs) + count_val(val, ys)
    decreases xs.len()
{
    if xs.len() == 0nat {
    } else {
        lemma_count_val_append(val, xs.drop_first(), ys);
    }
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
{
    /* code modified by LLM (iteration 5): fixed nat literal comparisons throughout */
    let mut result = Vec::new();
    let mut non_zero_part = Vec::new();
    let mut zero_count = 0;
    
    let mut i = 0;
    while i < xs.len()
        invariant
            0 <= i <= xs.len(),
            zero_count == count_val(0, xs@.subrange(0, i as int)),
            is_subsequence(xs@.subrange(0, i as int).filter(|x: i32| x != 0), non_zero_part@),
            forall|j: int| 0 <= j < non_zero_part.len() ==> non_zero_part[j] != 0,
    {
        if xs[i] == 0 {
            zero_count = zero_count + 1;
        } else {
            non_zero_part.push(xs[i]);
        }
        i = i + 1;
    }
    
    result = non_zero_part;
    
    let mut j = 0;
    while j < zero_count
        invariant
            0 <= j <= zero_count,
            result.len() + j == xs.len(),
            forall|k: int| 0 <= k < result.len() ==> result[k] != 0,
            count_val(0, result@) == j,
    {
        result.push(0);
        j = j + 1;
    }
    
    proof {
        assert(result.len() == xs.len());
        assert(count_val(0, xs@) == zero_count);
        assert(count_val(0, result@) == zero_count);
    }
    
    result
}
// </vc-code>

}
fn main() {}