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
proof fn lemma_count_val_append(val: i32, xs: Seq<i32>, ys: Seq<i32>)
    ensures count_val(val, xs + ys) == count_val(val, xs) + count_val(val, ys)
    decreases xs.len()
{
    if xs.len() == 0 {
        assert(xs + ys =~= ys);
    } else {
        assert((xs + ys).drop_first() =~= xs.drop_first() + ys);
        lemma_count_val_append(val, xs.drop_first(), ys);
    }
}

proof fn lemma_is_subsequence_append(xs: Seq<i32>, ys: Seq<i32>, zs: Seq<i32>)
    requires is_subsequence(xs, ys)
    ensures is_subsequence(xs, ys + zs)
    decreases xs.len(), ys.len()
{
    if xs.len() == 0 {
    } else if ys.len() == 0 {
        assert((ys + zs).drop_first() =~= ys + zs.drop_first());
        lemma_is_subsequence_append(xs, ys, zs.drop_first());
    } else {
        if xs[0] == ys[0] {
            assert((ys + zs).drop_first() =~= ys.drop_first() + zs);
            lemma_is_subsequence_append(xs.drop_first(), ys.drop_first(), zs);
        } else {
            assert((ys + zs).drop_first() =~= ys.drop_first() + zs);
            lemma_is_subsequence_append(xs, ys.drop_first(), zs);
        }
    }
}

/* helper modified by LLM (iteration 5): Remove generic parameter and use spec_fn directly */
proof fn lemma_filter_is_subsequence(xs: Seq<i32>, pred: spec_fn(i32) -> bool)
    ensures is_subsequence(xs.filter(pred), xs)
    decreases xs.len()
{
    if xs.len() == 0 {
    } else {
        lemma_filter_is_subsequence(xs.drop_first(), pred);
        if pred(xs[0]) {
            assert(xs.filter(pred) =~= seq![xs[0]] + xs.drop_first().filter(pred));
        } else {
            assert(xs.filter(pred) =~= xs.drop_first().filter(pred));
        }
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
/* code modified by LLM (iteration 5): Use FnSpec constructor for spec_fn */
{
    let mut non_zeros = Vec::new();
    let mut zero_count: usize = 0;
    
    for i in 0..xs.len()
        invariant
            non_zeros@.len() + zero_count == i,
            zero_count == count_val(0, xs@.take(i as int)),
            non_zeros@ =~= xs@.take(i as int).filter(|x: i32| x != 0),
            is_subsequence(non_zeros@, xs@.take(i as int)),
    {
        if xs[i] == 0 {
            zero_count = zero_count + 1;
        } else {
            non_zeros.push(xs[i]);
        }
    }
    
    assert(xs@.take(xs.len() as int) =~= xs@);
    let pred = spec_fn(|x: i32| x != 0);
    lemma_filter_is_subsequence(xs@, pred);
    
    let mut result = Vec::with_capacity(xs.len());
    
    for i in 0..non_zeros.len()
        invariant
            result.len() == i,
            result@ =~= non_zeros@.take(i as int),
            is_subsequence(result@, non_zeros@),
    {
        result.push(non_zeros[i]);
    }
    
    assert(non_zeros@.take(non_zeros.len() as int) =~= non_zeros@);
    
    for i in 0..zero_count
        invariant
            result.len() == non_zeros.len() + i,
            result@ =~= non_zeros@ + Seq::new(i as nat, |j: int| 0),
            count_val(0, result@) == i,
            is_subsequence(non_zeros@, result@),
    {
        result.push(0);
        proof {
            assert(result@ =~= non_zeros@ + Seq::new((i + 1) as nat, |j: int| 0));
            lemma_is_subsequence_append(non_zeros@, non_zeros@, Seq::new((i + 1) as nat, |j: int| 0));
        }
    }
    
    proof {
        lemma_count_val_append(0, non_zeros@, Seq::new(zero_count as nat, |j: int| 0));
        assert(count_val(0, non_zeros@) == 0);
        assert(count_val(0, Seq::new(zero_count as nat, |j: int| 0)) == zero_count);
    }
    
    result
}
// </vc-code>

}
fn main() {}