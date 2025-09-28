// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn hermite_to_power_basis(c: Seq<i8>, k: nat) -> Seq<i8>
    decreases c.len() - k
{
    if k >= c.len() {
        c
    } else if k == c.len() - 1 {
        c
    } else {
        let mut result = c;
        result = result.update(k as int, (2 * c[k as int] as int) as i8);
        if k + 2 < c.len() {
            result = result.update((k + 2) as int, (c[(k + 2) as int] as int - c[k as int] as int) as i8);
        }
        hermite_to_power_basis(result, k + 1)
    }
}

/* helper modified by LLM (iteration 5): Fixed requires clause to use old(c) consistently */
fn convert_hermite_step(c: &mut Vec<i8>, k: usize)
    requires
        old(c).len() > 0,
        k < old(c).len() - 1,
    ensures
        c.len() == old(c).len(),
        c[k as int] as int == 2 * old(c)[(k + 1) as int] as int,
        k + 2 < c.len() ==> c[(k + 2) as int] as int == old(c)[(k + 2) as int] as int - old(c)[k as int] as int,
        forall|i: int| 0 <= i < c.len() && i != k as int && i != (k + 2) as int ==> c[i] == old(c)[i],
{
    let temp = c[k];
    c.set(k, 2i8 * c[k + 1]);
    if k + 2 < c.len() {
        c.set(k + 2, c[k + 2] - temp);
    }
}
// </vc-helpers>

// <vc-spec>
fn herm2poly(c: Vec<i8>) -> (result: Vec<i8>)
    requires c.len() > 0,
    ensures
        result.len() == c.len(),
        /* Sanity checks */
        c.len() == 1 ==> result@ == c@,
        c.len() == 2 ==> result[0] == c[0] && result[1] as int == 2 * c[1] as int,
        /* Example from documentation: herm2poly([1, 2.75, 0.5, 0.375]) approximated with integers */
        (c.len() == 4 && c[0] as int == 1 && c[1] as int == 3 && c[2] as int == 1 && c[3] as int == 0) ==>
            (result[0] as int == 0 && result[1] as int == 1 && result[2] as int == 2 && result[3] as int == 3)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Implementation unchanged from iteration 4 */
    let mut result = c.clone();
    let n = result.len();
    
    if n == 1 {
        return result;
    }
    
    let mut k: usize = 0;
    while k < n - 1
        invariant
            result.len() == c.len(),
            result.len() == n,
            k <= n - 1,
    {
        convert_hermite_step(&mut result, k);
        k = k + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}