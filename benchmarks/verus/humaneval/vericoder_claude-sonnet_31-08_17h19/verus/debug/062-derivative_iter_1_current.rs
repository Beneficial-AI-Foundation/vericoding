use vstd::prelude::*;

verus! {

// <vc-helpers>

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
        return Some(Vec::new());
    }
    
    let mut result = Vec::new();
    let mut i = 1;
    
    while i < xs.len()
        invariant
            i <= xs@.len(),
            result@.len() == i - 1,
            forall|j: int| 0 <= j < result@.len() ==> #[trigger] result@[j] == (j + 1) * xs@[j + 1],
    {
        let coeff = i * xs[i];
        result.push(coeff);
        i += 1;
    }
    
    assert(result@.len() == xs@.len() - 1);
    assert(forall|j: int| 0 <= j < result@.len() ==> #[trigger] result@[j] == (j + 1) * xs@[j + 1]);
    
    proof {
        let derivative_seq = xs@.map(|i: int, x| i * x).skip(1);
        assert(derivative_seq.len() == xs@.len() - 1);
        assert(forall|j: int| 0 <= j < derivative_seq.len() ==> 
            #[trigger] derivative_seq[j] == (j + 1) * xs@[j + 1]);
        assert(derivative_seq =~= result@.map_values(|x| x as int));
    }
    
    Some(result)
}
// </vc-code>

fn main() {}
}