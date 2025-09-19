// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count_numbers_with_repeated_digits(n: u32) -> (result: u32)
    requires n > 0,
    ensures 
        result <= n,
        (n > 0 && n < 10) ==> result == 0,
        n == 20 ==> result == 1,
        n == 100 ==> result == 10,
        n == 1000 ==> result == 262,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}
fn main() {
    // let test1 = count_numbers_with_repeated_digits(20);
    // assert(test1 == 1);
    // let test2 = count_numbers_with_repeated_digits(100);
    // assert(test2 == 10);
    // let test3 = count_numbers_with_repeated_digits(1000);
    // assert(test3 == 262);
}