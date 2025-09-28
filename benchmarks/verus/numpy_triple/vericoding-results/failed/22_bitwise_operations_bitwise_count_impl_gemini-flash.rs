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
/* helper modified by LLM (iteration 5): provide an executable version of popcount and make it ghost for easier verification */
fn exec_popcount(n: u32) -> (count: nat)
    ensures count == popcount(n as nat)
{
    let mut count = 0u32;
    let mut temp_n = n;
    while temp_n > 0
        invariant
            temp_n >= 0,
            count >= 0,
            (count as nat) + popcount(temp_n as nat) == popcount(n as nat),
        decreases temp_n
    {
        if temp_n % 2 == 1 {
            count = count + 1;
        }
        temp_n = temp_n / 2;
    }
    count as nat
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
/* code modified by LLM (iteration 5): Corrected type issues (u33 to u32) and ghost casting */
{
    let mut result_vec = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i,
            i <= x.len(),
            result_vec.len() == i,
            forall|j: int| 0 <= j < i ==> result_vec[j] == popcount(abs_spec(x[j])),
        decreases x.len() - i
    {
        let val = x.get(i).unwrap();
        let abs_val_exec: u32;
        if val >= 0 {
             abs_val_exec = val as u32;
        } else {
             abs_val_exec = (-val) as u32;
        }
        result_vec.push(exec_popcount(abs_val_exec));
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}