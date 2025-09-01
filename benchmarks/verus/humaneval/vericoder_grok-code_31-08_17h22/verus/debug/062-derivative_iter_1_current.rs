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
    for i in 1..xs@.len() {
        let prod_int = (i as int) * (xs@[i] as int);
        if prod_int > usize::MAX as int {
            return None;
        }
        result.push(prod_int as usize);
    }
    proof {
        let expected = xs@.map(|#[trigger] i: int, x: usize| i * (x as int)).skip(1);
        assert result@.len() == expected.len();
        assert forall |j: int| 0 <= j && j < result@.len()
            implies #[trigger] ((j + 1) * (xs@[j + 1] as int)) == expected@[j]
            && result@[j] as int == expected@[j];
    }
    Some(result)
}
// </vc-code>

fn main() {}
}