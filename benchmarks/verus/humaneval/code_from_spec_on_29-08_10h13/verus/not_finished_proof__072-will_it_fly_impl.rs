use vstd::prelude::*;

verus! {

// pure-end

spec fn spec_sum(s: Seq<u32>) -> (ret:int) {
    s.fold_left(0, |x: int, y| x + y)
}
// pure-end

// <vc-helpers>
fn is_palindrome(v: &Vec<u32>) -> (ret: bool)
    ensures ret <==> v@ =~= v@.reverse()
{
    let len = v.len();
    let mut i = 0;
    while i < len / 2
        invariant 
            0 <= i <= len / 2,
            forall|k: int| 0 <= k < i ==> v@[k] == v@[len - 1 - k]
    {
        if v[i] != v[len - 1 - i] {
            return false;
        }
        i += 1;
    }
    
    proof {
        /* code modified by LLM (iteration 5): replaced ==> with implies */
        assert forall|k: int| 0 <= k < len implies v@[k] == v@[len - 1 - k] by {
            if k < len / 2 {
                // covered by loop invariant
            } else if k >= (len + 1) / 2 {
                let j = len - 1 - k;
                assert(0 <= j < len / 2);
                assert(v@[j] == v@[len - 1 - j]);
                assert(v@[k] == v@[j]);
            } else {
                // middle element(s) when len is odd
                assert(k == len - 1 - k);
            }
        };
    }
    
    true
}

fn sum_vec(v: &Vec<u32>) -> (ret: u32)
    requires spec_sum(v@) <= u32::MAX
    ensures ret as int == spec_sum(v@)
{
    let mut sum: u32 = 0;
    let mut i = 0;
    while i < v.len()
        invariant 
            0 <= i <= v.len(),
            sum as int == spec_sum(v@.subrange(0, i as int)),
            sum as int <= spec_sum(v@)
    {
        sum = sum + v[i];
        i += 1;
    }
    sum
}
// </vc-helpers>

// <vc-description>
/*
docstring: Implement will it fly.
*/
// </vc-description>

// <vc-spec>
fn will_it_fly(qs: &Vec<u32>, w: u32) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> qs@ =~= qs@.reverse() && spec_sum(qs@) <= w,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    /* code modified by LLM (iteration 5): moved ghost condition to proof block */
    proof {
        if spec_sum(qs@) > u32::MAX {
            return false;
        }
    }
    
    let is_pal = is_palindrome(qs);
    let sum = sum_vec(qs);
    let sum_ok = sum <= w;
    
    is_pal && sum_ok
}
// </vc-code>

}
fn main() {}