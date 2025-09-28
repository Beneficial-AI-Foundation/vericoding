// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): proof of mod properties for i8 */
fn mod_properties(a: i8, b: i8)
    requires
        b != 0,
    ensures
        a == (a / b) * b + a % b,
        (b > 0 ==> 0 <= a % b && a % b < b),
        (b < 0 ==> a % b <= 0 && a % b > b),
{
    proof {
        assert(a == (a / b) * b + a % b);
        assert(b > 0 ==> 0 <= a % b && a % b < b);
        assert(b < 0 ==> a % b <= 0 && a % b > b);
    }
}

// </vc-helpers>

// <vc-spec>
fn numpy_mod(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] != 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            #[trigger] result[i] == x1[i] % x2[i],
        forall|i: int| 0 <= i < result.len() ==> {
            let r = #[trigger] result[i];
            let a = x1[i];
            let b = x2[i];
            /* Basic remainder property: a = floor_div(a, b) * b + r */
            a == (a / b) * b + r &&
            /* Result has same sign as divisor (when divisor is non-zero) */
            (b > 0 ==> r >= 0 && r < b) &&
            (b < 0 ==> r <= 0 && r > b)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct result vector elementwise using i8 modulo with safe assertions */
    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            0 <= i as int && i as int <= x1.len() as int,
            res.len() == i,
            forall|j: int| 0 <= j && j < i as int ==> res[j] == x1[j] % x2[j],
        decreases x1.len() - i
    {
        let a: i8 = x1[i];
        let b: i8 = x2[i];
        let r: i8 = a % b;
        proof {
            assert(x1.len() == x2.len());
            assert(i < x2.len());
            assert(x2[i] != 0);
            mod_properties(a, b);
        }
        res.push(r);
        i = i + 1;
    }
    res
}

// </vc-code>


}
fn main() {}