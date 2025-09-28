// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

fn poly_leg_helper(c: &Vec<f32>, result: &mut Vec<f32>, i: usize)
    requires
        0 <= i <= c.len(),
        result.len() == c.len(),
        forall|k: int| 0 <= k < i ==> result@[k] == c@[k],
    ensures
        result.len() == c.len(),
        forall|k: int| 0 <= k < c.len() as int ==> result@[k] == c@[k],
{
    if i < c.len() {
        result.set(i, c[i]);
        poly_leg_helper(c, result, i + 1);
    }
}

proof fn length_invariant_lemma(c: Vec<f32>)
    requires
        c.len() > 0,
    ensures
        (c.len() as int) > 0,
{
    // The ensures condition is satisfied by the requires condition
}

/* helper modified by LLM (iteration 5): Fixed result.len() requirement and used set() instead of indexing */
// </vc-helpers>

// <vc-spec>
fn leg2poly(c: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == c.len(),

        (c.len() as int) < 3 ==> forall|i: int| 0 <= i < (c.len() as int) ==> result[i] == c[i],

        (c.len() as int) > 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Avoided reserve_exact, used Vec::new() and explicit initialization */
    if c.len() == 0 {
        let result = Vec::new();
        return result;
    }
    
    proof {
        length_invariant_lemma(c);
    }
    
    if c.len() < 3 {
        // Case where len < 3: create vector with correct capacity and push elements
        let mut result = Vec::new();
        let mut i: usize = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                result.len() == i,
                forall|k: int| 0 <= k < i ==> result@[k] == c@[k],
        {
            result.push(c[i]);
            i = i + 1;
        }
        result
    } else {
        // Initialize result with correct length using loop and push
        let mut result = Vec::new();
        let mut j: usize = 0;
        while j < c.len()
            invariant
                0 <= j <= c.len(),
                result.len() == j,
        {
            result.push(0.0f32);
            j = j + 1;
        }
        
        // Use helper to copy values
        poly_leg_helper(&c, &mut result, 0);
        result
    }
}
// </vc-code>

}
fn main() {}