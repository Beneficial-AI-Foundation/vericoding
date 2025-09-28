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
/* helper modified by LLM (iteration 5): Changed to exec fn with |result| in ensures to fix compilation error where 'result' was not in scope. */
fn pow(base: i64, exp: usize) -> i64
    requires
        exp <= 10,
    ensures |result|
        (result as int) == pow_int((base as int), exp as nat),
{
    if exp == 0 {
        1
    } else {
        (base * pow(base, (exp - 1) as usize)) as i64
    }
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
/* code modified by LLM (iteration 5): Maintained implementation with nested loops and proof blocks to handle vander matrix creation correctly. */
{
    let mut result: Vec<Vec<i8>> = Vec::new();
    proof {
        assert(result@.len() == 0);
    }
    for i in 0..x.len()
        invariant
            result@.len() == i as int,
            forall|k: int| 0 <= k < result@.len() ==> result@[k]@.len() == m,
            forall|k: int, j: int| 0 <= k < result@.len() && 0 <= j < m ==> 
                result@[k]@[j] as int == pow_int(x@[k as int] as int, (m - 1 - j) as nat),
    {
        let mut row: Vec<i8> = Vec::new();
        proof {
            assert(row@.len() == 0);
        }
        for j in 0..m
            invariant
                row@.len() == j as int,
                forall|jj: int| 0 <= jj < row@.len() ==> 
                    row@[jj] as int == pow_int(x@[i as int] as int, (m - 1 - jj) as nat),
        {
            let power = pow(x[i] as i64, (m - 1 - j) as usize);
            row.push(power as i8);
            proof {
                assert(row@.len() == j as int + 1);
                assert(row@[j as int] == (power as i8));
                assert(power as int == pow_int(x@[i as int] as int, (m - 1 - j) as nat));
                assert((power as i8) as int == power as int);
            }
        }
        result.push(row);
        proof {
            assert(result@.len() == i as int + 1);
        }
    }
    result
}
// </vc-code>


}
fn main() {}