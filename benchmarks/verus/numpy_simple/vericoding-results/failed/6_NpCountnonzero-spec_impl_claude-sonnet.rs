// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn nonzero_helper_skip_lemma(arr: Seq<f32>)
    requires arr.len() > 0
    ensures
        arr[0] == 0.0f32 ==> nonzero_helper(arr) == nonzero_helper(arr.skip(1)),
        arr[0] != 0.0f32 ==> nonzero_helper(arr) == nonzero_helper(arr.skip(1)) + 1
{
    if arr[0] == 0.0f32 {
        assert(nonzero_helper(arr) == nonzero_helper(arr.skip(1)));
    } else {
        assert(nonzero_helper(arr) == nonzero_helper(arr.skip(1)) + 1);
    }
}

proof fn nonzero_helper_monotonic(arr: Seq<f32>)
    ensures nonzero_helper(arr) <= arr.len()
    decreases arr.len()
{
    if arr.len() == 0 {
        assert(nonzero_helper(arr) == 0);
    } else {
        nonzero_helper_monotonic(arr.skip(1));
        assert(nonzero_helper(arr.skip(1)) <= arr.skip(1).len());
        if arr[0] == 0.0f32 {
            assert(nonzero_helper(arr) == nonzero_helper(arr.skip(1)));
        } else {
            assert(nonzero_helper(arr) == nonzero_helper(arr.skip(1)) + 1);
        }
    }
}

/* helper modified by LLM (iteration 5): fixed logical assertions for sequence extension */
proof fn nonzero_helper_take_extend(arr: Seq<f32>, i: int)
    requires 0 <= i < arr.len()
    ensures
        arr[i] == 0.0f32 ==> nonzero_helper(arr.take(i + 1)) == nonzero_helper(arr.take(i)),
        arr[i] != 0.0f32 ==> nonzero_helper(arr.take(i + 1)) == nonzero_helper(arr.take(i)) + 1
{
    let prefix = arr.take(i);
    let extended = arr.take(i + 1);
    
    if i == 0 {
        assert(prefix.len() == 0);
        assert(extended.len() == 1);
        assert(extended[0] == arr[0]);
        if arr[0] == 0.0f32 {
            assert(nonzero_helper(extended) == nonzero_helper(extended.skip(1)));
            assert(extended.skip(1).len() == 0);
            assert(nonzero_helper(extended.skip(1)) == 0);
            assert(nonzero_helper(prefix) == 0);
        } else {
            assert(nonzero_helper(extended) == nonzero_helper(extended.skip(1)) + 1);
            assert(extended.skip(1).len() == 0);
            assert(nonzero_helper(extended.skip(1)) == 0);
            assert(nonzero_helper(extended) == 1);
            assert(nonzero_helper(prefix) == 0);
        }
    } else {
        assert(extended.len() == prefix.len() + 1);
        assert(extended[extended.len() - 1] == arr[i]);
        assert(extended.drop_last() == prefix);
        
        if arr[i] == 0.0f32 {
            assert(extended[extended.len() - 1] == 0.0f32);
            assert(nonzero_helper(extended) == nonzero_helper(extended.drop_last()));
        } else {
            assert(extended[extended.len() - 1] != 0.0f32);
            assert(nonzero_helper(extended) == nonzero_helper(extended.drop_last()) + 1);
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
    /* code modified by LLM (iteration 5): fixed assertion paths and loop reasoning */
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    proof {
        nonzero_helper_monotonic(arr@);
    }
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            count <= i,
            count == nonzero_helper(arr@.take(i as int))
        decreases arr.len() - i
    {
        if arr[i] != 0.0f32 {
            proof {
                nonzero_helper_take_extend(arr@, i as int);
                assert(arr@[i as int] != 0.0f32);
            }
            count = count + 1;
        } else {
            proof {
                nonzero_helper_take_extend(arr@, i as int);
                assert(arr@[i as int] == 0.0f32);
            }
        }
        i = i + 1;
    }
    
    proof {
        assert(arr@.take(arr.len() as int) == arr@);
    }
    
    count
}
// </vc-code>


}
fn main() {}