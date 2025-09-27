// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        n * factorial((n - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn get_permutation(n: usize, k: usize) -> (result: Vec<char>)
    requires
        n >= 1,
        n <= 9,
        k >= 1,
        k <= factorial(n as nat),
    ensures
        result.len() == n,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {
    // let perm = get_permutation(3, 3);
    // println!("{:?}", perm); // Should output ['2', '1', '3']
    // let perm = get_permutation(4, 9);
    // println!("{:?}", perm); // Should output ['2', '3', '1', '4']
    // let perm = get_permutation(2, 2);
    // println!("{:?}", perm); // Should output ['2', '1']
}