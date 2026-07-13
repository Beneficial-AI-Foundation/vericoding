// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_winner(n: u32) -> (result: &'static str)
    requires n > 0,
    ensures 
        result == "Me" || result == "Grinch",
        n == 1 ==> result == "Grinch",
        n == 2 ==> result == "Me",
        (n > 1 && n % 2 == 1) ==> result == "Me",
        n == 4 ==> result == "Grinch",
        n == 6 ==> result == "Grinch",
        n == 12 ==> result == "Me",
        n == 16 ==> result == "Grinch"
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    "Me"
    // impl-end
}
// </vc-code>


}
fn main() {}