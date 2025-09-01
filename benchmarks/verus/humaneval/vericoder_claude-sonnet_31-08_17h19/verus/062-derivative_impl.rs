use vstd::prelude::*;

verus! {

// <vc-helpers>
lemma derivative_map_equivalence(xs: Seq<usize>, result: Seq<usize>)
    requires
        result.len() == xs.len() - 1,
        forall|j: int| 0 <= j < result.len() ==> result[j] == (j + 1) * xs[j + 1],
    ensures
        xs.map(|i: int, x| i * x).skip(1) =~= result.map_values(|x| x as int),
{
    let derivative_seq = xs.map(|i: int, x| i * x).skip(1);
    assert(derivative_seq.len() == result.len());
    
    assert(forall|j: int| 0 <= j < derivative_seq.len() ==> 
        derivative_seq[j] == xs.map(|i: int, x| i * x)[j + 1]);
    
    assert(forall|j: int| 0 <= j < derivative_seq.len() ==> 
        derivative_seq[j] == (j + 1) * xs[j + 1]);
    
    assert(forall|j: int| 0 <= j < result.len() ==> 
        derivative_seq[j] == result[j]);
    
    assert(derivative_seq =~= result.map_values(|x| x as int));
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
            1 <= i <= xs@.len(),
            result@.len() == i - 1,
            forall|j: int| 0 <= j < result@.len() ==> #[trigger] result@[j] == (j + 1) * xs@[j + 1],
        decreases xs.len() - i
    {
        let coeff = (i as usize) * xs[i];
        result.push(coeff);
        i += 1;
    }
    
    assert(result@.len() == xs@.len() - 1);
    assert(forall|j: int| 0 <= j < result@.len() ==> #[trigger] result@[j] == (j + 1) * xs@[j + 1]);
    
    proof {
        derivative_map_equivalence(xs@, result@);
    }
    
    Some(result)
}
// </vc-code>

fn main() {}
}