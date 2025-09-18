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
/* helper modified by LLM (iteration 5): fixed nat literal syntax by removing nat suffix */
fn compute_popcount(n: u32) -> (count: nat)
    ensures count == popcount(n as nat)
    decreases n
{
    let mut count: nat = 0;
    let mut val = n;
    while val > 0
        invariant count + popcount(val as nat) == popcount(n as nat)
        decreases val
    {
        if val % 2 == 1 {
            count = count + 1;
        }
        val = val / 2;
    }
    count
}

fn abs_to_u32(x: i32) -> (result: u32)
    ensures result as nat == abs_spec(x)
{
    if x >= 0 {
        x as u32
    } else {
        (-x) as u32
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
    /* code modified by LLM (iteration 5): fixed nat arithmetic by removing nat suffix from literals */
    let mut result: Vec<nat> = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            result.len() == i,
            i <= x.len(),
            forall|j: int| 0 <= j < i ==> result[j] == popcount(abs_spec(x[j]))
    {
        let abs_val = abs_to_u32(x[i]);
        let count = compute_popcount(abs_val);
        result.push(count);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}