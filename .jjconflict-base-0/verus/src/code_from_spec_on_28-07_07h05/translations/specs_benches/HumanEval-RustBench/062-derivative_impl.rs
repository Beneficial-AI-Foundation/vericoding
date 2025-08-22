use vstd::prelude::*;

verus! {

fn derivative(xs: &Vec<usize>) -> (ret: Option<Vec<usize>>)
    // post-conditions-start
    ensures
        ret.is_some() ==> xs@.len() == 0 || xs@.map(|i: int, x| i * x).skip(1)
            =~= ret.unwrap()@.map_values(|x| x as int),
    // post-conditions-end
{
    if xs.len() == 0 {
        return Some(Vec::new());
    }
    
    let mut result = Vec::new();
    let mut i = 1;
    
    /* code modified by LLM (iteration 3): added explicit trigger annotation for quantifier */
    while i < xs.len()
        invariant
            i <= xs.len(),
            result@.len() == i - 1,
            forall|j: int| 0 <= j < result@.len() ==> {
                let derivative_val = (j + 1) * (xs@[j + 1] as int);
                derivative_val >= 0 && derivative_val <= usize::MAX as int &&
                result@[j] as int == derivative_val
            } by {
                // Trigger on result@[j] to help inference
                result@[j];
            },
        decreases xs.len() - i,
    {
        /* code modified by LLM (iteration 2): simplified overflow check using only usize operations */
        // Check for overflow: if i * xs[i] would overflow usize
        if xs[i] > 0 && i > usize::MAX / xs[i] {
            return None;
        }
        
        let coeff = i * xs[i];
        result.push(coeff);
        i += 1;
    }
    
    /* code modified by LLM (iteration 2): kept ghost assertions for verification */
    assert(result@.len() == xs@.len() - 1);
    assert(forall|j: int| 0 <= j < result@.len() ==> 
        result@[j] as int == (j + 1) * (xs@[j + 1] as int));
    
    // Prove the postcondition holds
    assert(xs@.map(|i: int, x| i * x).skip(1) =~= result@.map_values(|x| x as int)) by {
        let derivative_spec = xs@.map(|i: int, x| i * x).skip(1);
        let result_as_int = result@.map_values(|x| x as int);
        
        assert(derivative_spec.len() == result_as_int.len());
        assert(forall|j: int| 0 <= j < derivative_spec.len() ==> 
            derivative_spec[j] == result_as_int[j]) by {
            assert(forall|j: int| 0 <= j < result@.len() ==> {
                let spec_val = xs@.map(|i: int, x| i * x)[j + 1];
                let result_val = result_as_int[j];
                spec_val == (j + 1) * (xs@[j + 1] as int) &&
                result_val == result@[j] as int &&
                result@[j] as int == (j + 1) * (xs@[j + 1] as int)
            });
        }
    };
    
    Some(result)
}

}
fn main() {}