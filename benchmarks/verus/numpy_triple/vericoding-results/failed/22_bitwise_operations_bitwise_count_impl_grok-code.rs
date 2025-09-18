// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_spec(x: i32) -> nat {
    if x >= 0 { x as nat } else { (-x) as nat }
}

spec fn popcount(n: nat) -> nat 
    decreases n
{
    if n == 0 {
        0
    } else {
        (n % 2) + popcount(n / 2)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): empty helpers as no need */
// </vc-helpers>

// <vc-spec>
fn bitwise_count(x: Vec<i32>) -> (result: Vec<nat>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == popcount(abs_spec(x[i])),
        forall|i: int| 0 <= i < result.len() ==> x[i] == 0 ==> result[i] == 0,
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): used tracked variables for ghost computations to avoid 'nat' type in exec code */
    let mut result: Vec<nat> = Vec::new();
    for i in 0..x.len() {
        let val = x[i];
        tracked let abs_input: nat = abs_spec(val);
        let mut n_exec: u32 = if val >= 0 { val as u32 } else { (-(val as i64)) as u32 };
        tracked let mut n_ghost: nat = abs_input;
        tracked let mut count: nat = 0;
        while n_exec > 0
            invariant
                0 <= count,
                count + popcount(n_ghost) == popcount(abs_input),
            decreases n_ghost
        {
            tracked {
                let bit = n_exec % 2;
                count += bit as nat;
                n_exec /= 2;
                n_ghost /= 2;
            }
        }
        proof {
            assert(count == popcount(abs_input));
        }
        result.push(count);
    }
    result
}
// </vc-code>

}
fn main() {}