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
/* helper modified by LLM (iteration 4): changed to proof fn to handle ghost return type nat */
proof fn abs_exec(x: i32) -> (result: nat)
    ensures result == abs_spec(x)
{
    if x >= 0 {
        x as nat
    } else {
        (-x) as nat
    }
}

/* helper modified by LLM (iteration 5): fixed compilation error by replacing while loop with recursion */
proof fn popcount_exec(n: nat) -> (count: nat)
    ensures count == popcount(n)
    decreases n
{
    if n == 0 {
        0
    } else {
        vstd::arithmetic::internals::div_mod_auto(n, 2);
        (n % 2) + popcount_exec(n / 2)
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
/* code modified by LLM (iteration 5): replaced imperative loop with functional vstd::vec::map_spec for proof-mode function */
{
    let result = vstd::vec::map_spec(x, |val: i32| popcount(abs_spec(val)));
    result
}
// </vc-code>

}
fn main() {}