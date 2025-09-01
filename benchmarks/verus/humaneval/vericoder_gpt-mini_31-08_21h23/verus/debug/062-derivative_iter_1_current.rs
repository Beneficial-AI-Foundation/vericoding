use vstd::prelude::*;

verus! {

// <vc-helpers>
// helper section left intentionally empty
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
    // impl-start
    let n: usize = xs.len();
    let mut out: Vec<usize> = Vec::new();
    let mut pos: usize = 1usize;
    while pos < n {
        invariant pos >= 1usize;
        invariant pos <= n || pos == 1usize;
        invariant out@.len() == pos - 1usize;
        invariant forall |k: int|
            0 <= k && k < (out@.len() as int) ==>
                out@[k] == ((k + 1) as usize) * xs@[k + 1];
        let xi_ref = xs.get(pos).unwrap();
        let xi: usize = *xi_ref;
        out.push(pos * xi);
        pos = pos + 1;
    }

    let res = Some(out);
    proof {
        if res.is_some() {
            let rv = res.as_ref().unwrap();
            // length equality
            assert(rv@.len() == if xs@.len() == 0 { 0 } else { xs@.len() - 1 });
            // element-wise equality (as ints)
            assert(forall |k: int|
                0 <= k && k < (rv@.len() as int) ==>
                    (rv@[k] as int) == ((k + 1) * xs@[k + 1])
            );
            // conclude mapped equality
            assert(rv@.map_values(|x: usize| x as int) =~= xs@.map(|i: int, x: usize| i * x).skip(1));
        }
    }
    res
    // impl-end
}
// </vc-code>

fn main() {}
}