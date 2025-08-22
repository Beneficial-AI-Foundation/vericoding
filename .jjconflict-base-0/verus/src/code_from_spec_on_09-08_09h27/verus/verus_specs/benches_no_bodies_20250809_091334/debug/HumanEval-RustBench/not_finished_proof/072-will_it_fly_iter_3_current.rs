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
    if i == j {
        // Base case: spec_sum(s.subrange(0, i)) == spec_sum(s.subrange(0, j))
    } else {
        // Inductive case: we can show that adding elements increases the sum
        lemma_increasing_sum_params(s, i, j - 1);
        // Now we know spec_sum(s.subrange(0, i)) <= spec_sum(s.subrange(0, j - 1))
        // And spec_sum(s.subrange(0, j)) = spec_sum(s.subrange(0, j - 1)) + s[j - 1]
        // Since s[j - 1] is u32 (non-negative), the sum can only increase or stay the same
    }
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
    // We can prove this by using our parameterized lemma for all valid i, j pairs
    assert forall|i: int, j: int| 0 <= i <= j <= s.len() implies spec_sum(s.subrange(0, i)) <= spec_sum(s.subrange(0, j)) by {
        lemma_increasing_sum_params(s, i, j);
    };
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
    
    while i < qs.len()
        invariant
            0 <= i <= qs.len(),
            sum == spec_sum(qs@.subrange(0, i as int)),
            sum <= u64::MAX,
        decreases qs.len() - i,
    {
        let old_sum = sum;
        sum = sum + qs[i] as u64;
        if sum > w as u64 {
            return false;
        }
        i += 1;
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
    
    /* code modified by LLM (iteration 1): added trigger annotation to fix quantifier trigger inference error */
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            forall|k: int| #![trigger qs@[k], qs@[len - 1 - k]] 0 <= k < i ==> qs@[k] == qs@[len - 1 - k],
        decreases len / 2 - i,
    {
        if qs[i] != qs[len - 1 - i] {
            return false;
        }
        i += 1;
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