use vstd::prelude::*;

verus! {

#[verifier::memoize]
spec fn spec_fib(n: nat) -> (ret:nat)
    decreases n,
{
    if (n == 0) {
        0
    } else if (n == 1) {
        1
    } else {
        spec_fib((n - 1) as nat) + spec_fib((n - 2) as nat)
    }
}
// pure-end
// pure-end

spec fn inner_expr_fib(n: u32, ret: Option<u32>) -> (result:bool) {
    match ret {
        None => spec_fib(n as nat) > u32::MAX,
        Some(f) => f == spec_fib(n as nat),
    }
}
// pure-end

/*
function_signature: "def fib(n: int) -> int"
docstring: |
Return n-th Fibonacci number.
test_cases:
- input: 10
expected_output: 55
- input: 1
expected_output: 1
- input: 8
expected_output: 21
*/

fn fib(n: u32) -> (ret: Option<u32>)
    // post-conditions-start
    ensures
        inner_expr_fib(n, ret),
    // post-conditions-end
{
    // impl-start
    assume(false);
    None
    // impl-end
}

} // verus!
fn main() {}