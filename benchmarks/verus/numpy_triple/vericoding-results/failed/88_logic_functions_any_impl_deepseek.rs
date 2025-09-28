// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed predicate syntax with ! */
predicate is_non_zero(x: f32) -> bool {
    x != 0.0f32
}

proof fn any_lemma(v: Vec<f32>, result: bool)
    ensures
        (result == true <==> exists|i: int| 0 <= i < v@.len() && is_non_zero(v@[i])),
        (result == false <==> forall|i: int| 0 <= i < v@.len() ==> !is_non_zero(v@[i]))
{
    if result {
        assert(exists|i: int| 0 <= i < v@.len() && is_non_zero(v@[i]));
    } else {
        assert(forall|i: int| 0 <= i < v@.len() ==> !is_non_zero(v@[i]));
    }
}
// </vc-helpers>

// <vc-spec>
fn any(v: Vec<f32>) -> (result: bool)
    ensures 
        (result == true <==> exists|i: int| 0 <= i < v@.len() && v@[i] != 0.0f32) &&
        (result == false <==> forall|i: int| 0 <= i < v@.len() ==> v@[i] == 0.0f32) &&
        (v@.len() == 0 ==> result == false) &&
        (forall|i: int| 0 <= i < v@.len() ==> v@[i] == 0.0f32 ==> result == false) &&
        (exists|i: int| 0 <= i < v@.len() && v@[i] != 0.0f32 ==> result == true) &&
        (result == true || result == false) &&
        !(result == true && result == false)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error with predicate syntax */
    let mut result = false;
    let mut index: usize = 0;
    let n = v.len();
    
    while index < n
        invariant
            0 <= index <= n,
            result == (exists|i: int| 0 <= i < index && v@[i] != 0.0f32),
            result == false ==> forall|i: int| 0 <= i < index ==> v@[i] == 0.0f32
        decreases n - index
    {
        let current = v[index];
        if current != 0.0f32 {
            result = true;
            break;
        }
        index += 1;
    }
    
    any_lemma(v, result);
    result
}
// </vc-code>

}
fn main() {}