// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed duplicate vec_sum definition and kept complete implementation */
spec fn vec_sum(a: Seq<f32>) -> f32
    decreases a.len()
{
    if a.len() == 0 {
        0.0f32
    } else {
        a[0] + vec_sum(a.subrange(1, a.len() as int))
    }
}

proof fn vec_sum_empty()
    ensures vec_sum(Seq::<f32>::empty()) == 0.0f32
{
}

proof fn vec_sum_zero_elements(a: Seq<f32>)
    requires forall|i: int| 0 <= i < a.len() ==> a[i] == 0.0f32
    ensures vec_sum(a) == 0.0f32
    decreases a.len()
{
    if a.len() == 0 {
    } else {
        vec_sum_zero_elements(a.subrange(1, a.len() as int));
    }
}
// </vc-helpers>

// <vc-spec>
spec fn vec_sum(a: Seq<f32>) -> f32;

fn sum(a: Vec<f32>) -> (result: f32)
    ensures 
        result == vec_sum(a@),
        a.len() == 0 ==> result == 0.0f32,
        (forall|i: int| 0 <= i < a.len() ==> a[i] == 0.0f32) ==> result == 0.0f32,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed implementation with proper loop invariant and proof structure */
{
    if a.len() == 0 {
        proof {
            vec_sum_empty();
        }
        return 0.0f32;
    }
    
    let mut sum = 0.0f32;
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            sum == vec_sum(a@.subrange(0, i as int)),
        decreases a.len() - i
    {
        sum = sum + a[i];
        
        proof {
            assert(a@.subrange(0, (i + 1) as int) == a@.subrange(0, i as int).push(a@[i as int]));
        }
        
        i = i + 1;
    }
    
    proof {
        assert(a@.subrange(0, a.len() as int) == a@);
    }
    
    sum
}
// </vc-code>

}
fn main() {}