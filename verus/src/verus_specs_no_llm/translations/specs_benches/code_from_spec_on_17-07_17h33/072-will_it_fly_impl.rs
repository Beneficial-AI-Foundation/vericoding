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
{
    return false;  // TODO: Remove this line and implement the function body
}
    // post-conditions-start
    ensures
        ret <==> spec_sum(qs@) <= w,
    // post-conditions-end
{
    /* code modified by LLM (iteration 1): Fixed function structure and moved ensures clause to signature */
    let mut sum: u64 = 0;
    let mut i = 0;
    while i < qs.len()
        invariant
            0 <= i <= qs.len(),
            sum == spec_sum(qs@.subrange(0, i as int)),
            sum <= u32::MAX as u64,
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
{
    return false;  // TODO: Remove this line and implement the function body
}
    // post-conditions-start
    ensures
        ret <==> qs@ =~= qs@.reverse(),
    // post-conditions-end
{
    /* code modified by LLM (iteration 1): Fixed function structure and moved ensures clause to signature */
    let mut left = 0;
    let mut right = qs.len();
    
    while left < right
        invariant
            0 <= left <= right <= qs.len(),
            forall|k: int| 0 <= k < left ==> qs@[k] == qs@[qs.len() - 1 - k],
            forall|k: int| right <= k < qs.len() ==> qs@[k] == qs@[qs.len() - 1 - k],
    {
        right = right - 1;
        if qs[left] != qs[right] {
            return false;
        }
        left = left + 1;
    }
    true
}

fn will_it_fly(qs: &Vec<u32>, w: u32) -> (ret: bool)
{
    return false;  // TODO: Remove this line and implement the function body
}
    // post-conditions-start
    ensures
        ret <==> qs@ =~= qs@.reverse() && spec_sum(qs@) <= w,
    // post-conditions-end
{
    /* code modified by LLM (iteration 1): Fixed function structure and moved ensures clause to signature */
    palindrome(qs) && sum_lesser_than_limit(qs, w)
}

}
fn main() {}