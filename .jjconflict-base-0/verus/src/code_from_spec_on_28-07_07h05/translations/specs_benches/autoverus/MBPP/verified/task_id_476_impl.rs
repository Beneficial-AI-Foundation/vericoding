use vstd::math::*;
use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

spec fn max_rcur(seq: Seq<i32>) -> int
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        max(seq.last() as int, max_rcur(seq.drop_last()))
    }
}

spec fn min_rcur(seq: Seq<i32>) -> int
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        min(seq.last() as int, min_rcur(seq.drop_last()))
    }
}

/* code modified by LLM (iteration 2): added helper lemma to prove max_rcur equivalence */
proof fn lemma_max_rcur_subrange_full(seq: Seq<i32>)
    requires seq.len() > 0,
    ensures max_rcur(seq.subrange(0, seq.len() as int)) == max_rcur(seq),
{
    assert(seq.subrange(0, seq.len() as int) =~= seq);
}

/* code modified by LLM (iteration 2): added helper lemma to prove min_rcur equivalence */
proof fn lemma_min_rcur_subrange_full(seq: Seq<i32>)
    requires seq.len() > 0,
    ensures min_rcur(seq.subrange(0, seq.len() as int)) == min_rcur(seq),
{
    assert(seq.subrange(0, seq.len() as int) =~= seq);
}

/* code modified by LLM (iteration 2): fixed lemma to properly establish max_rcur extension property */
proof fn lemma_max_rcur_extend(seq: Seq<i32>, i: int)
    requires 
        seq.len() > 0,
        1 <= i < seq.len(),
    ensures 
        max_rcur(seq.subrange(0, i + 1)) == max(seq[i] as int, max_rcur(seq.subrange(0, i))),
    decreases i,
{
    let sub_i = seq.subrange(0, i);
    let sub_i_plus_1 = seq.subrange(0, i + 1);
    
    if i == 1 {
        assert(sub_i.len() == 1);
        assert(sub_i_plus_1.len() == 2);
        assert(sub_i_plus_1.last() == seq[1]);
        assert(sub_i_plus_1.drop_last() =~= sub_i);
        assert(max_rcur(sub_i_plus_1) == max(sub_i_plus_1.last() as int, max_rcur(sub_i_plus_1.drop_last())));
        assert(max_rcur(sub_i_plus_1) == max(seq[1] as int, max_rcur(sub_i)));
    } else {
        assert(sub_i_plus_1.len() >= 2);
        assert(sub_i_plus_1.last() == seq[i]);
        assert(sub_i_plus_1.drop_last() =~= sub_i);
        assert(max_rcur(sub_i_plus_1) == max(sub_i_plus_1.last() as int, max_rcur(sub_i_plus_1.drop_last())));
        assert(max_rcur(sub_i_plus_1) == max(seq[i] as int, max_rcur(sub_i)));
    }
}

/* code modified by LLM (iteration 2): fixed lemma to properly establish min_rcur extension property */
proof fn lemma_min_rcur_extend(seq: Seq<i32>, i: int)
    requires 
        seq.len() > 0,
        1 <= i < seq.len(),
    ensures 
        min_rcur(seq.subrange(0, i + 1)) == min(seq[i] as int, min_rcur(seq.subrange(0, i))),
    decreases i,
{
    let sub_i = seq.subrange(0, i);
    let sub_i_plus_1 = seq.subrange(0, i + 1);
    
    if i == 1 {
        assert(sub_i.len() == 1);
        assert(sub_i_plus_1.len() == 2);
        assert(sub_i_plus_1.last() == seq[1]);
        assert(sub_i_plus_1.drop_last() =~= sub_i);
        assert(min_rcur(sub_i_plus_1) == min(sub_i_plus_1.last() as int, min_rcur(sub_i_plus_1.drop_last())));
        assert(min_rcur(sub_i_plus_1) == min(seq[1] as int, min_rcur(sub_i)));
    } else {
        assert(sub_i_plus_1.len() >= 2);
        assert(sub_i_plus_1.last() == seq[i]);
        assert(sub_i_plus_1.drop_last() =~= sub_i);
        assert(min_rcur(sub_i_plus_1) == min(sub_i_plus_1.last() as int, min_rcur(sub_i_plus_1.drop_last())));
        assert(min_rcur(sub_i_plus_1) == min(seq[i] as int, min_rcur(sub_i)));
    }
}

//IMPL sum_min_max
fn sum_min_max(arr: &Vec<i32>) -> (sum: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    ensures
        sum == max_rcur(arr@) + min_rcur(arr@),
{
    let mut max_val = arr[0];
    let mut min_val = arr[0];
    let mut i = 1;
    
    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            max_val == max_rcur(arr@.subrange(0, i as int)),
            min_val == min_rcur(arr@.subrange(0, i as int)),
            i32::MIN / 2 < max_val < i32::MAX / 2,
            i32::MIN / 2 < min_val < i32::MAX / 2,
        decreases arr.len() - i,
    {
        proof {
            lemma_max_rcur_extend(arr@, i as int);
            lemma_min_rcur_extend(arr@, i as int);
        }
        
        if arr[i] > max_val {
            max_val = arr[i];
        }
        if arr[i] < min_val {
            min_val = arr[i];
        }
        i += 1;
    }
    
    proof {
        lemma_max_rcur_subrange_full(arr@);
        lemma_min_rcur_subrange_full(arr@);
    }
    
    max_val + min_val
}

} // verus!

The key changes made:

   - `subrange(0, i+1).last() == seq[i]`
   - `subrange(0, i+1).drop_last() =~= subrange(0, i)`
   - The recursive definition applies correctly



The lemmas now properly establish that extending a subrange by one element follows the expected recursive pattern, which allows the loop invariants to be maintained correctly.