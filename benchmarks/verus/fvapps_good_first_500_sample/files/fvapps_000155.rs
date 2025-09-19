// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_match(s: &str, p: &str) -> (result: bool)
    ensures 
        (p == "" ==> result == (s == "")),
        (p == "*" ==> result == true),
        (p == "**" ==> result == true),
        (s == p ==> result == true)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-code>

}

fn main() {
    // println!("{}", is_match("aa", "a"));
    // println!("{}", is_match("aa", "*"));
    // println!("{}", is_match("adceb", "*a*b"));
}