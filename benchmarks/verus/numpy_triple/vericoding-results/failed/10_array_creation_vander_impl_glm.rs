// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn pow_int(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * pow_int(base, (exp - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): changed exp parameter from nat to usize and adjusted loop accordingly */
fn exec_pow(base: i8, exp: usize) -> (result: i8)
    ensures
        result as int == pow_int(base as int, exp as nat),
{
    let mut res: i64 = 1;
    let mut i: usize = 0;
    while i < exp
        invariant
            i <= exp,
            res == pow_int(base as int, i as nat) as i64,
        decreases exp - i,
    {
        res = res * (base as i64);
        i = i + 1;
    }
    res as i8
}
// </vc-helpers>

// <vc-spec>
fn vander(x: Vec<i8>, m: usize) -> (result: Vec<Vec<i8>>)
    requires 
        x@.len() > 0,
        m > 0,
    ensures
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i]@.len() == m,
        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < m ==> 
            result@[i]@[j] as int == pow_int(x@[i] as int, (m - 1 - j) as nat),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): replaced nat with usize for exponent calculation */
{
    let n = x.len();
    let mut result = Vec::new();
    for i in 0..n {
        let mut row = Vec::new();
        for j in 0..m {
            let exp = m - 1 - j;
            let power = exec_pow(x[i], exp);
            row.push(power);
        }
        result.push(row);
    }
    result
}
// </vc-code>


}
fn main() {}