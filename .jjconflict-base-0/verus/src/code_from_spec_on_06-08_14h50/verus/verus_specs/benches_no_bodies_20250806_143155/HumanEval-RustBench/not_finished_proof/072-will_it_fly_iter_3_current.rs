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
    let mut sum: u64 = 0;
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i < qs.len()
        invariant
            0 <= i <= qs.len(),
            sum == spec_sum(qs@.subrange(0, i as int)),
            sum <= u32::MAX as u64,
        decreases qs.len() - i,
    {
        if sum > w as u64 {
            return false;
        }
        sum = sum + qs[i] as u64;
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
    let len = qs.len();
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            forall|k: int| 0 <= k < i ==> qs@[k] == qs@[len - 1 - k],
        decreases len / 2 - i,
    {
        if qs[i] != qs[len - 1 - i] {
            return false;
        }
        i = i + 1;
    }
    proof {
        /* code modified by LLM (iteration 1): replaced ==> with implies in assert forall */
        assert forall|k: int| 0 <= k < len implies qs@[k] == qs@.reverse()[k] by {
            if 0 <= k < len {
                if k < len / 2 {
                    assert(qs@[k] == qs@[len - 1 - k]);
                    assert(qs@.reverse()[k] == qs@[len - 1 - k]);
                } else {
                    let mirror_k = len - 1 - k;
                    assert(0 <= mirror_k < len / 2);
                    assert(qs@[mirror_k] == qs@[len - 1 - mirror_k]);
                    assert(qs@[mirror_k] == qs@[k]);
                    assert(qs@.reverse()[k] == qs@[len - 1 - k]);
                    assert(qs@.reverse()[k] == qs@[mirror_k]);
                }
            }
        }
        assert(qs@ =~= qs@.reverse());
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