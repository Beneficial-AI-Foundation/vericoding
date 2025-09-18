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
/* helper modified by LLM (iteration 5): proves prefix concatenation yields subsequence */
proof fn lemma_concat_prefix_subseq(xs: Seq<i32>, ys: Seq<i32>)
    ensures
        is_subsequence(xs, xs + ys),
    decreases xs.len()
{
    if xs.len() == 0 {
    } else {
        // (xs + ys) starts with xs[0] and its tail is xs.drop_first() + ys
        assert((xs + ys)[0] == xs[0]);
        assert((xs + ys).drop_first() == xs.drop_first() + ys);
        lemma_concat_prefix_subseq(xs.drop_first(), ys);
    }
}

/* helper modified by LLM (iteration 5): counts split across concatenation */
proof fn lemma_count_split(val: i32, xs: Seq<i32>, ys: Seq<i32>)
    ensures
        count_val(val, xs + ys) == count_val(val, xs) + count_val(val, ys),
    decreases xs.len()
{
    if xs.len() == 0 {
    } else {
        // Relate head/tail of concatenation to heads/tails of components
        assert((xs + ys)[0] == xs[0]);
        assert((xs + ys).drop_first() == xs.drop_first() + ys);
        // Inductive hypothesis on the tail of xs
        lemma_count_split(val, xs.drop_first(), ys);
        if xs[0] == val {
            // Expand definitions according to count_val
            assert(count_val(val, xs + ys) == count_val(val, (xs + ys).drop_first()) + 1);
            assert(count_val(val, xs) == count_val(val, xs.drop_first()) + 1);
            // Use inductive equality on the tails
            assert(count_val(val, (xs + ys).drop_first()) == count_val(val, xs.drop_first()) + count_val(val, ys));
            // Combine to reach the desired equality
            assert(count_val(val, xs + ys) == (count_val(val, xs.drop_first()) + count_val(val, ys)) + 1);
            assert(count_val(val, xs + ys) == count_val(val, xs) + count_val(val, ys));
        } else {
            // Head is not counted; both sides omit the head
            assert(count_val(val, xs + ys) == count_val(val, (xs + ys).drop_first()));
            assert(count_val(val, xs) == count_val(val, xs.drop_first()));
            assert(count_val(val, (xs + ys).drop_first()) == count_val(val, xs.drop_first()) + count_val(val, ys));
            assert(count_val(val, xs + ys) == count_val(val, xs) + count_val(val, ys));
        }
    }
}

/* helper modified by LLM (iteration 5): proves a sequence is subsequence of any prefix concatenated before it (ys + xs) */
proof fn lemma_concat_suffix_subseq(xs: Seq<i32>, ys: Seq<i32>)
    ensures
        is_subsequence(xs, ys + xs),
    decreases ys.len()
{
    if ys.len() == 0 {
    } else {
        // (ys + xs).drop_first() == ys.drop_first() + xs, so skip head of ys and apply IH
        assert((ys + xs).drop_first() == ys.drop_first() + xs);
        lemma_concat_suffix_subseq(xs, ys.drop_first());
    }
}

/* helper modified by LLM (iteration 5): filtered sequence containing only non-zeros has zero count 0 */
proof fn lemma_filter_no_zero(xs: Seq<i32>)
    ensures
        count_val(0, xs.filter(|x: i32| x != 0)) == 0,
    decreases xs.len()
{
    if xs.len() == 0 {
    } else {
        lemma_filter_no_zero(xs.drop_first());
        if xs[0] == 0 {
            // head discarded by the filter
            assert(xs.filter(|x: i32| x != 0) == xs.drop_first().filter(|x: i32| x != 0));
            assert(count_val(0, xs.filter(|x: i32| x != 0)) == count_val(0, xs.drop_first().filter(|x: i32| x != 0)));
        } else {
            // head kept but is non-zero, so it does not contribute to count_val(0,_)
            assert(xs.filter(|x: i32| x != 0)[0] == xs[0]);
            assert(xs.filter(|x: i32| x != 0).drop_first() == xs.drop_first().filter(|x: i32| x != 0));
            assert(count_val(0, xs.filter(|x: i32| x != 0)) == count_val(0, xs.drop_first().filter(|x: i32| x != 0)));
        }
        assert(count_val(0, xs.filter(|x: i32| x != 0)) == 0);
    }
}

/* helper modified by LLM (iteration 5): count of zeros in the filtered-zero subsequence equals count in original sequence */
proof fn lemma_filter_count_eq(xs: Seq<i32>)
    ensures
        count_val(0, xs.filter(|x: i32| x == 0)) == count_val(0, xs),
    decreases xs.len()
{
    if xs.len() == 0 {
    } else {
        lemma_filter_count_eq(xs.drop_first());
        if xs[0] == 0 {
            // head counted on both sides
            assert(xs.filter(|x: i32| x == 0)[0] == 0);
            assert(xs.filter(|x: i32| x == 0).drop_first() == xs.drop_first().filter(|x: i32| x == 0));
            assert(count_val(0, xs.filter(|x: i32| x == 0)) == count_val(0, xs.drop_first().filter(|x: i32| x == 0)) + 1);
            assert(count_val(0, xs) == count_val(0, xs.drop_first()) + 1);
            assert(count_val(0, xs.filter(|x: i32| x == 0)) == count_val(0, xs));
        } else {
            // head not counted on either side
            assert(xs.filter(|x: i32| x == 0) == xs.drop_first().filter(|x: i32| x == 0));
            assert(count_val(0, xs.filter(|x: i32| x == 0)) == count_val(0, xs.drop_first().filter(|x: i32| x == 0)));
            assert(count_val(0, xs) == count_val(0, xs.drop_first()));
            assert(count_val(0, xs.filter(|x: i32| x == 0)) == count_val(0, xs));
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
{
    /* code modified by LLM (iteration 5): build result by inserting zeros at front and pushing nonzeros to preserve order */
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0_usize;
    while i < xs.len()
        invariant
            0 <= i && i <= xs.len(),
            res.len() == i,
            res@ == xs@.take(i as int).filter(|x: i32| x == 0) + xs@.take(i as int).filter(|x: i32| x != 0),
        decreases xs.len() - i
    {
        let v = xs[i];
        if v == 0 {
            // insert zero at front so that zeros accumulate before nonzeros
            res.insert(0, 0);
        } else {
            // keep nonzeros in relative order by pushing at the end
            res.push(v);
        }
        i = i + 1_usize;
    }

    // Now res@ == xs@.filter(|x| x == 0) + xs@.filter(|x| x != 0)
    proof {
        let zeros_seq = xs@.filter(|x: i32| x == 0);
        let filtered = xs@.filter(|x: i32| x != 0);
        // from loop invariant at i == xs.len()
        assert(res@ == zeros_seq + filtered);
        // filtered is subsequence of zeros_seq + filtered
        lemma_concat_suffix_subseq(filtered, zeros_seq);
        assert(is_subsequence(filtered, res@));
        // count of zeros in res equals count(0, zeros_seq) + count(0, filtered)
        lemma_count_split(0, zeros_seq, filtered);
        assert(count_val(0, res@) == count_val(0, zeros_seq) + count_val(0, filtered));
        // filtered has no zeros
        lemma_filter_no_zero(filtered);
        assert(count_val(0, filtered) == 0);
        assert(count_val(0, res@) == count_val(0, zeros_seq));
        // count of zeros in original xs equals count of zeros_seq
        lemma_filter_count_eq(xs@);
        assert(count_val(0, xs@) == count_val(0, zeros_seq));
        assert(count_val(0, xs@) == count_val(0, res@));

        // ordering property: all zeros are before any non-zero in res
        let zl = zeros_seq.len();
        // if an element at index i is non-zero, show everything after it is non-zero
        assert(forall|ii: int|
            0 <= ii < res.len() && res[ii] != 0 ==>
                forall|jj: int| ii < jj < res.len() ==> res[jj] != 0
        );
    }

    res
}

// </vc-code>

}
fn main() {}