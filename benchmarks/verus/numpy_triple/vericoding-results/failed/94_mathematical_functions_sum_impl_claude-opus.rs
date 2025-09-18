// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed duplicate vec_sum definition that was causing compilation error */
proof fn vec_sum_empty()
    ensures vec_sum(Seq::<f32>::empty()) == 0.0f32,
{
}

proof fn vec_sum_append(a: Seq<f32>, x: f32)
    ensures vec_sum(a.push(x)) == vec_sum(a) + x,
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a.push(x) =~= Seq::<f32>::new(1, |i: int| x));
    } else {
        assert(a.push(x).subrange(1, (a.len() + 1) as int) =~= a.subrange(1, a.len() as int).push(x));
        vec_sum_append(a.subrange(1, a.len() as int), x);
    }
}

proof fn vec_sum_subrange_extend(a: Seq<f32>, i: int)
    requires 0 <= i < a.len(),
    ensures vec_sum(a.subrange(0, (i + 1) as int)) == vec_sum(a.subrange(0, i as int)) + a[i],
{
    let sub_i = a.subrange(0, i as int);
    let sub_i_plus_1 = a.subrange(0, (i + 1) as int);
    assert(sub_i_plus_1 =~= sub_i.push(a[i]));
    vec_sum_append(sub_i, a[i]);
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
{
    /* code modified by LLM (iteration 5): Implementation using loop to compute sum */
    let mut sum = 0.0f32;
    let mut i: usize = 0;
    
    proof {
        vec_sum_empty();
        assert(a@.subrange(0, 0) =~= Seq::<f32>::empty());
    }
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            sum == vec_sum(a@.subrange(0, i as int)),
        decreases a.len() - i,
    {
        proof {
            vec_sum_subrange_extend(a@, i as int);
        }
        sum = sum + a[i];
        i = i + 1;
    }
    
    assert(a@.subrange(0, a.len() as int) =~= a@);
    sum
}
// </vc-code>

}
fn main() {}