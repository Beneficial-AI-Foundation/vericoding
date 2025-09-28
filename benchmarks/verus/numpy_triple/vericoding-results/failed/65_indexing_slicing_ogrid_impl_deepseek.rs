// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix proof helpers with proper type handling and arithmetic verification */
predicate step_positive(step: int) {
    step > 0
}

predicate step_negative(step: int) {
    step < 0
}

proof fn range_validation_proof(start: int, stop: int, step: int, i: int, n: int)
    requires
        step != 0,
        0 <= i < n,
    ensures
        if step_positive(step) {
            start <= start + i * step && start + i * step < stop
        } else if step_negative(step) {
            stop < start + i * step && start + i * step <= start
        },
{
    if step > 0 {
        assert(step_positive(step));
        assert(start + i * step >= start);
        assert(start + i * step < stop);
    } else {
        assert(step_negative(step));
        assert(start + i * step <= start);
        assert(start + i * step > stop);
    }
}

pub closed spec fn in_range(val: int, start: int, stop: int, step: int) -> bool {
    if step > 0 {
        start <= val && val < stop
    } else {
        stop < val && val <= start
    }
}
// </vc-helpers>

// <vc-spec>
fn ogrid(start: i8, stop: i8, step: i8, n: usize) -> (result: Vec<i8>)
    requires 
        step != 0,
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result@[i] == start as int + i * (step as int),
        forall|i: int| 0 <= i < n ==> 
            if step > 0 { 
                (start as int) <= result@[i] && result@[i] < (stop as int)
            } else {
                (stop as int) < result@[i] && result@[i] <= (start as int)
            },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix type conversions, arithmetic safety, and while loop invariants */
{
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    
    ghost {
        range_validation_proof(start as int, stop as int, step as int, i as int, n as int);
    }
    
    while i < n
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (start as int) + j * (step as int),
            forall|j: int| 0 <= j < i ==> in_range(result@[j] as int, start as int, stop as int, step as int),
        decreases n - i
    {
        let computed = (start as i16).wrapping_add((step as i16).wrapping_mul(i as i16));
        assert(computed <= i8::MAX as i16 && computed >= i8::MIN as i16);
        let value = computed as i8;
        
        ghost {
            range_validation_proof(start as int, stop as int, step as int, i as int, n as int);
            assert(value as int == (start as int) + (i as int) * (step as int));
        }
        
        result.push(value);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}