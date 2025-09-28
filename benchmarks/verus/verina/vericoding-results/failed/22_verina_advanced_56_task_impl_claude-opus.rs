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
/* helper modified by LLM (iteration 3): Fixed filter lemmas with correct sequence operations and added helper for count_val properties */
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

proof fn lemma_count_val_take_extend(val: i32, xs: Seq<i32>, i: int)
    requires 0 <= i < xs.len()
    ensures 
        xs[i] == val ==> count_val(val, xs.take(i + 1)) == count_val(val, xs.take(i)) + 1,
        xs[i] != val ==> count_val(val, xs.take(i + 1)) == count_val(val, xs.take(i))
    decreases i
{
    assert(xs.take(i + 1) =~= xs.take(i) + seq![xs[i]]);
    lemma_count_val_append(val, xs.take(i), seq![xs[i]]);
    if xs[i] == val {
        assert(count_val(val, seq![xs[i]]) == 1);
    } else {
        assert(count_val(val, seq![xs[i]]) == 0);
    }
}

proof fn lemma_is_subsequence_refl(xs: Seq<i32>)
    ensures is_subsequence(xs, xs)
    decreases xs.len()
{
    if xs.len() == 0 {
    } else {
        lemma_is_subsequence_refl(xs.drop_first());
    }
}

proof fn lemma_is_subsequence_trans(xs: Seq<i32>, ys: Seq<i32>, zs: Seq<i32>)
    requires is_subsequence(xs, ys), is_subsequence(ys, zs)
    ensures is_subsequence(xs, zs)
    decreases xs.len() + ys.len() + zs.len()
{
    if xs.len() == 0 {
    } else if ys.len() == 0 {
        assert(false);
    } else if zs.len() == 0 {
        assert(false);
    } else {
        if xs[0] == ys[0] {
            if ys[0] == zs[0] {
                lemma_is_subsequence_trans(xs.drop_first(), ys.drop_first(), zs.drop_first());
            } else {
                lemma_is_subsequence_trans(xs, ys, zs.drop_first());
            }
        } else {
            lemma_is_subsequence_trans(xs, ys.drop_first(), zs);
        }
    }
}

proof fn lemma_filter_preserves_order(xs: Seq<i32>)
    ensures is_subsequence(xs.filter(|x: i32| x != 0), xs)
    decreases xs.len()
{
    if xs.len() == 0 {
        assert(xs.filter(|x: i32| x != 0) =~= Seq::empty());
    } else {
        let rest = xs.drop_first();
        lemma_filter_preserves_order(rest);
        
        if xs[0] != 0 {
            assert(xs.filter(|x: i32| x != 0) =~= seq![xs[0]] + rest.filter(|x: i32| x != 0));
        } else {
            assert(xs.filter(|x: i32| x != 0) =~= rest.filter(|x: i32| x != 0));
        }
    }
}

proof fn lemma_filter_take_extend(xs: Seq<i32>, i: int)
    requires 0 <= i < xs.len()
    ensures 
        xs[i] != 0 ==> xs.take(i + 1).filter(|x: i32| x != 0) =~= xs.take(i).filter(|x: i32| x != 0) + seq![xs[i]],
        xs[i] == 0 ==> xs.take(i + 1).filter(|x: i32| x != 0) =~= xs.take(i).filter(|x: i32| x != 0)
{
    assert(xs.take(i + 1) =~= xs.take(i) + seq![xs[i]]);
    assert((xs.take(i) + seq![xs[i]]).filter(|x: i32| x != 0) =~= 
           xs.take(i).filter(|x: i32| x != 0) + seq![xs[i]].filter(|x: i32| x != 0));
    if xs[i] != 0 {
        assert(seq![xs[i]].filter(|x: i32| x != 0) =~= seq![xs[i]]);
    } else {
        assert(seq![xs[i]].filter(|x: i32| x != 0) =~= Seq::empty());
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
/* code modified by LLM (iteration 3): Fixed loop invariants and added proper proof steps for count_val */
{
    let mut result = Vec::new();
    let mut zero_count: usize = 0;
    
    for i in 0..xs.len()
        invariant
            result.len() + zero_count == i,
            zero_count as int == count_val(0, xs@.take(i as int)),
            forall|j: int| 0 <= j < result.len() ==> result[j] != 0,
            result@ =~= xs@.take(i as int).filter(|x: i32| x != 0),
            is_subsequence(result@, xs@.take(i as int)),
    {
        if xs[i] != 0 {
            proof {
                lemma_filter_take_extend(xs@, i as int);
                assert(xs@.take((i + 1) as int).filter(|x: i32| x != 0) =~= result@ + seq![xs[i as int]]);
                lemma_count_val_take_extend(0, xs@, i as int);
            }
            result.push(xs[i]);
        } else {
            proof {
                lemma_filter_take_extend(xs@, i as int);
                assert(xs@.take((i + 1) as int).filter(|x: i32| x != 0) =~= result@);
                lemma_count_val_take_extend(0, xs@, i as int);
            }
            zero_count = zero_count + 1;
        }
    }
    
    let non_zero_count = result.len();
    proof {
        assert(zero_count == xs.len() - non_zero_count);
        assert(result@ =~= xs@.filter(|x: i32| x != 0));
        assert(count_val(0, result@) == 0);
    }
    
    for j in 0..zero_count
        invariant
            result.len() == non_zero_count + j,
            result.len() <= xs.len(),
            forall|k: int| 0 <= k < non_zero_count ==> result[k as int] != 0,
            forall|k: int| non_zero_count <= k < result.len() ==> result[k as int] == 0,
            count_val(0, result@) == j,
            result@.take(non_zero_count as int) =~= xs@.filter(|x: i32| x != 0),
    {
        proof {
            assert(result@ =~= result@.take(result.len() as int));
            assert(result@ + seq![0] =~= result@.take(result.len() as int) + seq![0]);
            lemma_count_val_append(0, result@, seq![0]);
            assert(count_val(0, seq![0]) == 1);
        }
        result.push(0);
    }
    
    proof {
        assert(xs@.take(xs.len() as int) =~= xs@);
        assert(result@.take(non_zero_count as int) =~= xs@.filter(|x: i32| x != 0));
        lemma_filter_preserves_order(xs@);
        assert(is_subsequence(xs@.filter(|x: i32| x != 0), xs@));
        assert(is_subsequence(result@.take(non_zero_count as int), result@));
        assert(count_val(0, xs@) == zero_count);
    }
    
    result
}
// </vc-code>

}
fn main() {}