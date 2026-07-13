// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count_vowel_permutation(n: nat) -> (result: nat)
    requires n > 0,
    ensures
        result > 0,
        result < 1000000007,
        n == 1 ==> result == 5,
        n == 2 ==> result == 10
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
    // let result1 = count_vowel_permutation(1);
    // println!("Result for n=1: {}", result1);
    
    // let result2 = count_vowel_permutation(2);
    // println!("Result for n=2: {}", result2);
    
    // let result5 = count_vowel_permutation(5);
    // println!("Result for n=5: {}", result5);
}