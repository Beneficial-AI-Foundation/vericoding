use vstd::prelude::*;

verus! {

// <vc-helpers>
//
// </vc-helpers>
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
    if (xs.len() == 0) {
        let mut result = Vec::new();
        Some(result)
    } else {
        let len = xs.len();
        let mut result = Vec::new();
        let mut i: usize = 1;
        while (i < len)
            invariant
                i >= 1,
                i <= len,
                result@.len() == (i - 1) as int,
                forall |k: int| 0 <= k < result@.len() ==> result@[k] as int == ((k + 1) as int) * (xs@[k + 1] as int)
            decreases len - i
        {
            let val = i * xs[i];
            result.push(val);
            proof {
                assert(result@.len() - 1 == (i - 1) as int);
                assert(result@[result@.len() - 1] as int == ((i as int)) * (xs@[i as int] as int));
            }
            i += 1;
        }
        assert(result@.map_values(|x| x as int) =~= xs@.map(|i: int, x: usize| (i as int) * (x as int)).skip(1));
        Some(result)
    }
}
// </vc-code>

fn main() {}
}