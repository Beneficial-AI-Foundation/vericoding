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
/* helper modified by LLM (iteration 5): Corrected type issues and `add` method usage. */
prairie_runtime_defs!{

fn popcount_exec(n_param: nat) -> nat {
    let mut count: nat = 0; // Initialize count as nat
    let mut num: nat = n_param; // Initialize num as nat
    while num > 0
        invariant
            num >= 0,
            count <= n_param,
            num + count == n_param + popcount(num),
            num.is_constant() || num.broadcast_as_array().len() == 1
    {
        if num % 2 == 1 {
            count = count + 1;
        }
        num = num / 2;
    }
    count
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
/* code modified by LLM (iteration 5): No change needed, previous fix was correct. */
{
    let mut result_vec = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result_vec.len() == i,
            forall|j: int| 0 <= j < i ==> result_vec[j] == popcount(abs_spec(x[j]))
    {
        result_vec.push(popcount_exec(abs_spec(x[i])));
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}