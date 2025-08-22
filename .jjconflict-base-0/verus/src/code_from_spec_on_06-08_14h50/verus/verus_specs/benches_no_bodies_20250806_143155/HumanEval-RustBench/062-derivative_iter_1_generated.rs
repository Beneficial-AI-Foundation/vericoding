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
    
    while i < xs.len()
        invariant
            i >= 1,
            i <= xs.len(),
            result@.len() == i - 1,
            forall|j: int| 0 <= j < result@.len() ==> result@[j] == ((j + 1) * xs@[j + 1]) as usize,
    {
        let coeff = i * xs[i];
        result.push(coeff);
        i += 1;
    }
    
    Some(result)
}

}
fn main() {}