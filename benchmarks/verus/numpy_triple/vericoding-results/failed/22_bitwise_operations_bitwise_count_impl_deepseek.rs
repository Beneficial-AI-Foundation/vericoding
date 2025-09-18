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
/* helper modified by LLM (iteration 5): fix nat usage in exec code */
fn abs(x: i32) -> (result: u32)
    requires
        x != -2147483648,
    ensures
        result == abs_spec(x),
{
    if x >= 0 {
        x as u32
    } else {
        (0 - x) as u32
    }
}

fn count_bits(n: u32) -> (count: u32)
    ensures
        count as nat == popcount(n as nat),
    decreases n,
{
    if n == 0 {
        0
    } else {
        let remainder = n % 2;
        let quotient = n / 2;
        let sub_count = count_bits(quotient);
        let count_val = if remainder == 0 { 0 } else { 1 };
        count_val + sub_count
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
/* code modified by LLM (iteration 5): adapt to u32 return type from count_bits */
{
    let mut result: Vec<nat> = Vec::with_capacity(x.len());
    let mut idx: usize = 0;

    while idx < x.len()
        invariant
            0 <= idx <= x.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < result.len() ==> result[i] == popcount(abs_spec(x[i])),
            forall|i: int| 0 <= i < result.len() ==> x[i] == 0 ==> result[i] == 0,
            forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
    {
        let current = x[idx];
        let abs_val = abs(current);
        proof {
            assert(abs_val == abs_spec(current));
        }
        let count_u32 = count_bits(abs_val);
        let count: nat = count_u32 as nat;
        result.push(count);
        idx = idx + 1;
    }
    result
}
// </vc-code>

}
fn main() {}