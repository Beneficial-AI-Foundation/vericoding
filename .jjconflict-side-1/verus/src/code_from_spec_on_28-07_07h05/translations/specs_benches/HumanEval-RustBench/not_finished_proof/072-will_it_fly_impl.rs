use vstd::prelude::*;

verus! {

proof fn lemma_increasing_sum_params(s: Seq<u32>, i: int, j: int)
    // pre-conditions-start
    requires
        0 <= i <= j <= s.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        spec_sum(s.subrange(0, i)) <= spec_sum(s.subrange(0, j)),
    decreases j - i,
    // post-conditions-end
{
    // impl-start
    if (i < j) {
        assert(spec_sum(s.subrange(0, j - 1)) <= spec_sum(s.subrange(0, j))) by {
            assert(s.subrange(0, j).drop_last() == s.subrange(0, j - 1));
        }
        lemma_increasing_sum_params(s, i, j - 1);
    }
    // impl-end
}
// pure-end

proof fn lemma_increasing_sum(s: Seq<u32>)
    // post-conditions-start
    ensures
        forall|i: int, j: int|
            #![trigger spec_sum(s.subrange(0, i)), spec_sum(s.subrange(0, j))]
            0 <= i <= j <= s.len() ==> spec_sum(s.subrange(0, i)) <= spec_sum(s.subrange(0, j)),
    // post-conditions-end
{
    // impl-start
    assert forall|i: int, j: int|
        #![trigger spec_sum(s.subrange(0, i)), spec_sum(s.subrange(0, j))]
        0 <= i <= j <= s.len() ==> spec_sum(s.subrange(0, i)) <= spec_sum(s.subrange(0, j)) by {
        if (0 <= i <= j <= s.len()) {
            lemma_increasing_sum_params(s, i, j);
        }
    }
    // impl-end
}
// pure-end

spec fn spec_sum(s: Seq<u32>) -> (ret:int) {
    s.fold_left(0, |x: int, y| x + y)
}
// pure-end

fn sum_lesser_than_limit(qs: &Vec<u32>, w: u32) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> spec_sum(qs@) <= w,
    // post-conditions-end
{
    let mut sum = 0u64;
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added proof of sum overflow case and proper loop termination */
    while i < qs.len()
        invariant
            0 <= i <= qs.len(),
            sum == spec_sum(qs@.subrange(0, i as int)),
            sum <= u64::MAX,
        decreases qs.len() - i,
    {
        if sum > u64::MAX - qs[i] as u64 {
            /* code modified by LLM (iteration 1): fixed type casting for vector indexing */
            proof {
                lemma_increasing_sum(qs@);
                assert(spec_sum(qs@.subrange(0, i as int)) <= spec_sum(qs@));
                assert(sum as int > u64::MAX as int - qs[i as int] as int);
                assert(sum as int + qs[i as int] as int > u64::MAX as int);
                assert(spec_sum(qs@) >= sum as int + qs[i as int] as int);
                assert(spec_sum(qs@) > u64::MAX as int >= w as int);
            }
            return false;
        }
        sum = sum + qs[i] as u64;
        /* code modified by LLM (iteration 1): added proof that sum matches subrange after increment */
        proof {
            assert(qs@.subrange(0, (i + 1) as int) == qs@.subrange(0, i as int).push(qs@[i as int]));
        }
        i = i + 1;
    }
    
    sum <= w as u64
}

fn palindrome(qs: &Vec<u32>) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> qs@ =~= qs@.reverse(),
    // post-conditions-end
{
    let mut left = 0;
    let mut right = qs.len();
    
    /* code modified by LLM (iteration 1): fixed invariants and added proof for early return case */
    while left < right
        invariant
            0 <= left <= qs.len(),
            0 <= right <= qs.len(),
            left <= right,
            forall|k: int| #![trigger qs@[k]] 0 <= k < left ==> qs@[k] == qs@[qs@.len() - 1 - k],
            forall|k: int| #![trigger qs@[k]] right <= k < qs@.len() ==> qs@[qs@.len() - 1 - k] == qs@[k],
        decreases right - left,
    {
        right = right - 1;
        if qs[left] != qs[right] {
            /* code modified by LLM (iteration 1): added proof that mismatch means not palindrome */
            proof {
                assert(qs@[left as int] != qs@[right as int]);
                assert(qs@[left as int] != qs@[qs@.len() - 1 - left as int]);
                assert(!(qs@ =~= qs@.reverse()));
            }
            return false;
        }
        /* code modified by LLM (iteration 1): added proof that matching elements maintain palindrome property */
        proof {
            assert(qs@[left as int] == qs@[right as int]);
            assert(right as int == qs@.len() - 1 - left as int);
        }
        left = left + 1;
    }
    
    /* code modified by LLM (iteration 1): added proof that loop completion means palindrome */
    proof {
        assert(left >= right);
        assert forall|k: int| 0 <= k < qs@.len() implies qs@[k] == qs@[qs@.len() - 1 - k] by {
            if k < left {
                assert(qs@[k] == qs@[qs@.len() - 1 - k]);
            } else if k >= right {
                assert(qs@[qs@.len() - 1 - k] == qs@[k]);
            } else {
                assert(left <= k < right);
                assert(left >= right);
                assert(false);
            }
        }
    }
    
    true
}

fn will_it_fly(qs: &Vec<u32>, w: u32) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> qs@ =~= qs@.reverse() && spec_sum(qs@) <= w,
    // post-conditions-end
{
    palindrome(qs) && sum_lesser_than_limit(qs, w)
}

}
fn main() {}