use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
fn derivative(xs: &Vec<usize>) -> (ret: Option<Vec<usize>>)
    // post-conditions-start
    ensures
        ret.is_some() ==> xs@.len() == 0 || xs@.map(|i: int, x| i * x).skip(1)
            =~= ret.unwrap()@.map_values(|x| x as int),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if xs.len() == 0 {
        return None;
    }
    
    let mut result: Vec<usize> = Vec::new();
    let mut i: usize = 1;
    
    while i < xs.len()
        invariant
            1 <= i <= xs.len(),
            result@.len() == i - 1,
            forall|j: int| 0 <= j < result@.len() ==> #[trigger] result@[j] as int == (j + 1) * xs@[j + 1] as int,
        decreases xs.len() - i,
    {
        // Add proof to ensure no overflow
        proof {
            assert(i < xs.len());
            assert(0 <= i < usize::MAX);
            assert(0 <= xs[i] <= usize::MAX);
        }
        
        let val = (i as int * xs[i] as int) as usize;
        result.push(val);
        
        // Assert the invariant holds after push
        proof {
            assert(result@.len() == i);
            assert(forall|j: int| 0 <= j < i - 1 ==> result@[j] as int == (j + 1) * xs@[j + 1] as int);
            assert(result@[i - 1] as int == val as int);
            assert(val as int == i as int * xs@[i] as int);
            assert(result@[i - 1] as int == i as int * xs@[i] as int);
        }
        
        i = i + 1;
    }
    
    assert(result@.len() == xs@.len() - 1);
    assert forall|j: int| 0 <= j < result@.len() implies #[trigger] result@[j] as int == (j + 1) * xs@[j + 1] as int by {
        assert(0 <= j < xs@.len() - 1);
    }
    
    assert(xs@.map(|i: int, x| i * x).skip(1) =~= result@.map_values(|x| x as int)) by {
        let derivative_seq = xs@.map(|i: int, x| i * x).skip(1);
        let result_as_int = result@.map_values(|x| x as int);
        
        assert(derivative_seq.len() == result_as_int.len()) by {
            assert(xs@.map(|i: int, x| i * x).len() == xs@.len());
            assert(derivative_seq.len() == xs@.len() - 1);
            assert(result@.len() == xs@.len() - 1);
            assert(result_as_int.len() == result@.len());
        }
        
        assert forall|k: int| 0 <= k < result@.len() implies 
            derivative_seq[k] == result_as_int[k] by {
            assert(derivative_seq[k] == xs@.map(|i: int, x| i * x)[k + 1]);
            assert(xs@.map(|i: int, x| i * x)[k + 1] == (k + 1) * xs@[k + 1]);
            assert(result@[k] as int == (k + 1) * xs@[k + 1] as int);
            assert(result_as_int[k] == result@[k] as int);
        }
    }
    
    Some(result)
}
// </vc-code>

fn main() {}
}