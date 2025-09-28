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
/* helper modified by LLM (iteration 5): implemented proper inductive proofs for all lemmas */
proof fn lemma_subsequence_preserved(xs: Seq<i32>, ys: Seq<i32>, val: i32)
    requires is_subsequence(xs, ys)
    ensures is_subsequence(xs, ys.push(val))
    decreases xs.len() + ys.len()
{
    if xs.len() == 0 {
        // empty subsequence of any sequence
    } else if ys.len() == 0 {
        // contradiction with precondition
        assert(false);
    } else {
        let ys_extended = ys.push(val);
        if xs[0] == ys[0] {
            lemma_subsequence_preserved(xs.drop_first(), ys.drop_first(), val);
            assert(is_subsequence(xs.drop_first(), ys.drop_first().push(val)));
            assert(ys.drop_first().push(val) == ys_extended.drop_first());
        } else {
            lemma_subsequence_preserved(xs, ys.drop_first(), val);
            assert(is_subsequence(xs, ys.drop_first().push(val)));
            assert(ys.drop_first().push(val) == ys_extended.drop_first());
        }
    }
}

proof fn lemma_filter_subsequence(xs: Seq<i32>)
    ensures is_subsequence(xs.filter(|x: i32| x != 0), xs)
    decreases xs.len()
{
    if xs.len() == 0 {
        assert(xs.filter(|x: i32| x != 0).len() == 0);
    } else {
        let first = xs[0];
        let rest = xs.drop_first();
        lemma_filter_subsequence(rest);
        
        if first != 0 {
            assert(xs.filter(|x: i32| x != 0) == Seq::new(1, |_| first) + rest.filter(|x: i32| x != 0));
            assert(is_subsequence(rest.filter(|x: i32| x != 0), rest));
            assert(is_subsequence(Seq::new(1, |_| first) + rest.filter(|x: i32| x != 0), xs));
        } else {
            assert(xs.filter(|x: i32| x != 0) == rest.filter(|x: i32| x != 0));
            assert(is_subsequence(rest.filter(|x: i32| x != 0), rest));
            assert(is_subsequence(rest.filter(|x: i32| x != 0), xs));
        }
    }
}

proof fn lemma_count_val_preserved(xs: Seq<i32>, val: i32)
    ensures count_val(val, xs) == count_val(val, xs.filter(|x: i32| x != 0)) + count_val(val, xs.filter(|x: i32| x == 0))
    decreases xs.len()
{
    if xs.len() == 0 {
        assert(count_val(val, xs) == 0);
        assert(count_val(val, xs.filter(|x: i32| x != 0)) == 0);
        assert(count_val(val, xs.filter(|x: i32| x == 0)) == 0);
    } else {
        let first = xs[0];
        let rest = xs.drop_first();
        lemma_count_val_preserved(rest, val);
        
        if first != 0 {
            assert(xs.filter(|x: i32| x != 0) == Seq::new(1, |_| first) + rest.filter(|x: i32| x != 0));
            assert(xs.filter(|x: i32| x == 0) == rest.filter(|x: i32| x == 0));
        } else {
            assert(xs.filter(|x: i32| x != 0) == rest.filter(|x: i32| x != 0));
            assert(xs.filter(|x: i32| x == 0) == Seq::new(1, |_| first) + rest.filter(|x: i32| x == 0));
        }
    }
}

proof fn lemma_subsequence_filter_prefix(xs: Seq<i32>, i: int)
    requires 0 <= i <= xs.len()
    ensures is_subsequence(xs.take(i).filter(|x: i32| x != 0), xs.filter(|x: i32| x != 0))
    decreases i
{
    if i == 0 {
        assert(xs.take(0).filter(|x: i32| x != 0).len() == 0);
    } else {
        lemma_subsequence_filter_prefix(xs, i - 1);
        let prefix = xs.take(i);
        let shorter_prefix = xs.take(i - 1);
        
        if xs[i - 1] != 0 {
            assert(prefix.filter(|x: i32| x != 0) == shorter_prefix.filter(|x: i32| x != 0).push(xs[i - 1]));
            lemma_subsequence_preserved(shorter_prefix.filter(|x: i32| x != 0), xs.filter(|x: i32| x != 0).take(xs.filter(|x: i32| x != 0).len()), xs[i - 1]);
        } else {
            assert(prefix.filter(|x: i32| x != 0) == shorter_prefix.filter(|x: i32| x != 0));
        }
    }
}

proof fn lemma_zeros_at_end_property(result: Seq<i32>, non_zero_len: int)
    requires
        0 <= non_zero_len <= result.len(),
        forall|k: int| 0 <= k < non_zero_len ==> result[k] != 0,
        forall|k: int| non_zero_len <= k < result.len() ==> result[k] == 0
    ensures
        forall|i: int| 0 <= i < result.len() && result[i] != 0 ==>
            forall|j: int| i < j < result.len() ==> result[j] != 0
{
    // By contradiction: if there exists i with result[i] != 0 and j > i with result[j] == 0,
    // then by the precondition, i < non_zero_len and j >= non_zero_len, so i < j < non_zero_len
    // which contradicts j >= non_zero_len
    assert forall|i: int, j: int| 0 <= i < result.len() && result[i] != 0 && i < j < result.len() implies result[j] != 0 by {
        if result[i] != 0 {
            assert(i < non_zero_len);  // from precondition
            if j < result.len() && j > i {
                if j >= non_zero_len {
                    assert(result[j] == 0);  // from precondition
                    assert(false);  // contradiction
                } else {
                    assert(j < non_zero_len);
                    assert(result[j] != 0);  // from precondition
                }
            }
        }
    };
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
    /* code modified by LLM (iteration 5): fixed invariants and added proper proof structure */
    let mut result = Vec::new();
    let mut i = 0;
    
    // First pass: collect non-zero elements
    while i < xs.len()
        invariant
            0 <= i <= xs.len(),
            result.len() <= i,
            forall|k: int| 0 <= k < result.len() ==> result[k] != 0,
            is_subsequence(result@, xs@.take(i as int)),
            result@ == xs@.take(i as int).filter(|x: i32| x != 0),
        decreases xs.len() - i
    {
        if xs[i] != 0 {
            result.push(xs[i]);
        }
        i += 1;
        
        proof {
            lemma_subsequence_filter_prefix(xs@, i as int);
        }
    }
    
    // Capture the number of non-zero elements
    let non_zero_count = result.len();
    
    proof {
        assert(result@ == xs@.filter(|x: i32| x != 0));
        lemma_filter_subsequence(xs@);
    }
    
    // Second pass: add zeros to the end
    let zero_count = xs.len() - result.len();
    let mut j = 0;
    
    while j < zero_count
        invariant
            0 <= j <= zero_count,
            zero_count == xs.len() - non_zero_count,
            result.len() == non_zero_count + j,
            forall|k: int| 0 <= k < non_zero_count ==> result[k] != 0,
            forall|k: int| non_zero_count <= k < result.len() ==> result[k] == 0,
            result@.take(non_zero_count as int) == xs@.filter(|x: i32| x != 0),
        decreases zero_count - j
    {
        result.push(0);
        j += 1;
    }
    
    proof {
        // Establish all postconditions
        assert(result@.take(non_zero_count as int) == xs@.filter(|x: i32| x != 0));
        assert(is_subsequence(xs@.filter(|x: i32| x != 0), result@));
        
        lemma_zeros_at_end_property(result@, non_zero_count as int);
        
        // Count preservation
        lemma_count_val_preserved(xs@, 0);
        assert(count_val(0, xs@) == count_val(0, xs@.filter(|x: i32| x != 0)) + count_val(0, xs@.filter(|x: i32| x == 0)));
        assert(count_val(0, xs@.filter(|x: i32| x != 0)) == 0);
        assert(count_val(0, xs@) == count_val(0, xs@.filter(|x: i32| x == 0)));
        assert(count_val(0, result@) == j as nat);
        assert(count_val(0, xs@.filter(|x: i32| x == 0)) == (xs.len() - non_zero_count) as nat);
        assert(count_val(0, xs@) == count_val(0, result@));
    }
    
    result
}
// </vc-code>

}
fn main() {}