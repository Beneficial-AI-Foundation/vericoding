// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove nonzero_helper of full skip is zero */
proof fn nonzero_skip_empty(s: Seq<f32>)
    ensures
        nonzero_helper(s.skip(s.len() as int)) == 0,
    decreases s.len()
{
    if s.len() == 0 {
        // empty sequence: skip(0) == empty, nonzero_helper(empty) == 0 by definition
    } else {
        let s1 = s.skip(1);
        nonzero_skip_empty(s1);
        assert(s1.len() == s.len() - 1);
        assert(s.skip(s.len() as int) == s1.skip(s1.len() as int));
        assert(nonzero_helper(s1.skip(s1.len() as int)) == 0);
    }
}

/* helper modified by LLM (iteration 5): relate head element to helper of tail */
proof fn nonzero_head_relation(s: Seq<f32>)
    requires
        s.len() > 0,
    ensures
        if s[0] == 0.0f32 {
            nonzero_helper(s) == nonzero_helper(s.skip(1))
        } else {
            nonzero_helper(s) == 1 + nonzero_helper(s.skip(1))
        },
    decreases s.len()
{
    if s.len() == 0 {
        // unreachable due to requires, left for totality
    } else {
        let rest = s.skip(1);
        if s[0] == 0.0f32 {
            assert(nonzero_helper(s) == nonzero_helper(rest));
        } else {
            assert(nonzero_helper(s) == 1 + nonzero_helper(rest));
        }
    }
}
// </vc-helpers>

// <vc-spec>
spec fn nonzero_helper(arr: Seq<f32>) -> nat 
    decreases arr.len()
{
    if arr.len() == 0 {
        0
    } else {
        let rest_count = nonzero_helper(arr.skip(1));
        if arr[0] == 0.0f32 {
            rest_count
        } else {
            rest_count + 1
        }
    }
}

fn nonzero(arr: Vec<f32>) -> (result: usize)
    ensures 
        result <= arr.len(),
        result == nonzero_helper(arr@),
        arr.len() > 0 && arr[0] == 0.0f32 ==> 
            nonzero_helper(arr@.skip(1)) == if result > 0 { result - 1 } else { 0 }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate and maintain invariant that count + nonzero_helper(skip(i)) == total */
    let mut i: usize = 0;
    let mut count: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            count + nonzero_helper(arr@.skip(i as int)) == nonzero_helper(arr@),
        decreases arr.len() - i
    {
        if arr[i] == 0.0f32 {
            proof {
                // head is zero: nonzero_helper(skip(i)) == nonzero_helper(skip(i+1))
                nonzero_head_relation(arr@.skip(i as int));
                assert(nonzero_helper(arr@.skip(i as int)) == nonzero_helper(arr@.skip((i + 1) as int)));
            }
        } else {
            proof {
                // head is non-zero: nonzero_helper(skip(i)) == 1 + nonzero_helper(skip(i+1))
                nonzero_head_relation(arr@.skip(i as int));
                assert(nonzero_helper(arr@.skip(i as int)) == 1 + nonzero_helper(arr@.skip((i + 1) as int)));
                assert(count + 1 + nonzero_helper(arr@.skip((i + 1) as int)) == nonzero_helper(arr@));
                assert(count + 1 <= arr.len());
            }
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-code>


}
fn main() {}