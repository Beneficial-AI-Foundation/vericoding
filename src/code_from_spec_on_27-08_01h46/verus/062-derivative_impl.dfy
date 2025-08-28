use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn spec_derivative(xs: Seq<int>) -> Seq<int> {
    xs.map(|i: int, x| i * x).skip(1)
}
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
            forall|j: int| 0 <= j < result@.len() ==> result@[j] == ((j + 1) * xs@[j + 1]) as usize
        decreases xs@.len() - i
    {
        let derivative_val = i * xs[i];
        result.push(derivative_val);
        
        proof {
            assert(result@.len() == i);
            assert(result@[i-1] == derivative_val);
            assert(derivative_val == i * xs[i]);
            assert(derivative_val == ((i as int) * (xs[i] as int)) as usize);
        }
        
        i += 1;
    }
    
    Some(result)
}
// </vc-code>

}
fn main() {}