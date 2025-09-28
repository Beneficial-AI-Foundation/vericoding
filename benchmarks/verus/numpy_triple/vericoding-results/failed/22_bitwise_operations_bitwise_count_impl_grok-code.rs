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
exec fn abs_helper(x: i32) -> u32 {
    if x >= 0 { x as u32 } else { (-x) as u32 }
}
exec fn popcount_helper(n: u32) -> u32
    decreases n as int
{
    if n == 0 {
        0
    } else {
        ((n % 2) as u32) + popcount_helper(n / 2)
    }
}
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
    /* code modified by LLM (iteration 5): fixed cast syntax in tracked block */
    let mut result: Vec<nat> = Vec::new();
    for i in 0..x.len() {
        let abs_val_u = abs_helper(x[i]);
        let count_u = popcount_helper(abs_val_u);
        tracked {
            let val_nat: nat = count_u as int;
            result.push(val_nat);
        }
        proof {
            assert(abs_val_u as int == abs_spec(x[i]) as int);
            assert(count_u as int == popcount(abs_spec(x[i])) as int);
        }
    }
    result
}
// </vc-code>

}
fn main() {}