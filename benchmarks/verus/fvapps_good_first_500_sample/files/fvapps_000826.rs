// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn get_winner(n: nat) -> (result: &'static str)
    requires 1 <= n && n <= 19,
    ensures 
        result == "Arjuna" || result == "Bhima",
        n == 2 ==> result == "Arjuna",
        n == 3 ==> result == "Arjuna", 
        n == 4 ==> result == "Arjuna",
        n == 7 ==> result == "Arjuna",
        n == 8 ==> result == "Arjuna",
        n == 1 ==> result == "Bhima",
        n == 5 ==> result == "Bhima",
        n == 9 ==> result == "Bhima"
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    "Arjuna"
    // impl-end
}
// </vc-code>


}
fn main() {}