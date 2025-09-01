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
    let mut res = Vec::new();
    for i in 1..xs.len() {
        invariant res@ =~= xs@.map(|idx: int, x| (idx * x) as usize).skip(1).take(res.len())
        res.push((i * xs[i]) as usize);
    }
    Some(res)
}
// </vc-code>

fn main() {}
}