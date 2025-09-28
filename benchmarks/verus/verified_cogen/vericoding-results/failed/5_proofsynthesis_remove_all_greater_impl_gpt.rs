// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
spec fn is_at_most_e(x: i32, e: i32) -> bool { x <= e }
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)

    requires 
        forall |k1:int,k2:int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],

    ensures
        forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
        forall |k:int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]),
// </vc-spec>
// <vc-code>
{
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant 0 <= i <= v.len()
        invariant forall |k:int| 0 <= k < res.len() ==> res@[k] <= e && v@.contains(res@[k])
        invariant forall |j:int| 0 <= j < i ==> v@[j] <= e ==> res@.contains(v@[j])
        decreases v.len() - i
    {
        let x = v[i];
        if x <= e {
            res.push(x);
        }
        i += 1;
    }
    res
}
// </vc-code>

}
fn main() {}