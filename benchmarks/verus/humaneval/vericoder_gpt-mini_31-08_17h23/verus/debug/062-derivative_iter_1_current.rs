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
    let mut res: Vec<usize> = Vec::new();
    if n == 0 {
        return Some(res);
    }
    // now n >= 1
    let mut k: usize = 1;
    while k < n
        invariant 1 <= k && k <= n
        invariant res.len() == k - 1
        invariant forall |j: nat| j < res@.len() ==> (res@@[j] as int) == ((j as int + 1) * (xs@@[j + 1] as int))
    {
        let xk: usize = xs.get(k).unwrap();
        let v: usize = k * xk;
        res.push(v);
        k = k + 1;
    }
    proof {
        if n != 0 {
            // after loop, k == n and res.len() == n - 1
            assert(res.len() == n - 1);
            // prove sequence equality: xs@.map(|i:int, x| i * x).skip(1) =~= res@.map_values(|x| x as int)
            // show lengths equal
            assert(xs@.map(|i: int, x: usize| i * (x as int)).skip(1).len() == res@.len());
            // show elements equal
            assert(forall |j: nat| j < res@.len() ==>
                xs@.map(|i: int, x: usize| i * (x as int)).skip(1)@[j] == (res@@[j] as int)
            );
        }
    }
    Some(res)
    // impl-end
}
// </vc-code>

fn main() {}
}