use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
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
    if n == 0 {
        return Some(Vec::new());
    }
    let mut res: Vec<usize> = Vec::new();
    let mut i: usize = 1;
    while i < n
        invariant 1 <= i && i <= n;
        invariant res@.len() == i - 1;
        invariant forall |k: int| 0 <= k && k < res@.len() as int ==>
            res@.index(k as nat) as int == (k + 1) * xs@.index((k + 1) as nat) as int
        decreases n - i;
    {
        let prod: usize = i * xs[i];
        res.push(prod);
        proof {
            // The newly pushed element at index i-1 equals i * xs@[i]
            assert(res@.index((i - 1) as nat) as int == (i as int) * xs@.index(i as nat) as int);
        }
        i += 1;
    }
    proof {
        // Establish the postcondition sequence equality when n > 0.
        assert(res@.len() == n - 1);
        assert(forall |k: int| 0 <= k && k < res@.len() as int ==>
            res@.index(k as nat) as int == (k + 1) * xs@.index((k + 1) as nat) as int);
        assert(xs@.map(|i: int, x| i * x).skip(1) =~= res@.map_values(|x| x as int));
    }
    Some(res)
    // impl-end
}
// </vc-code>

fn main() {}
}