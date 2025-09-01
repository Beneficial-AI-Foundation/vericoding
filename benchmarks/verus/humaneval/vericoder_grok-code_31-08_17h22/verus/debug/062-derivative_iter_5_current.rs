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
    if xs@.len() == 0 {
        return Some(Vec::new());
    }
    let mut result = Vec::new();
    let expected_seq = xs@.map(|i: int, x: usize| i * (x as int)).skip(1);
    let mut i = 1;
    while i < xs@.len()
        invariant
            result@.len() == i - 1 &&
            forall |k: int| 0 <= k < result@.len() implies result@[k] as int == expected_seq@[k]
    {
        let prod_int = (i as int) * (xs@[i] as int);
        if prod_int > usize::MAX as int {
            return None;
        }
        result.push(prod_int as usize);
        i += 1;
    }
    Some(result)
}
// </vc-code>

fn main() {}
}