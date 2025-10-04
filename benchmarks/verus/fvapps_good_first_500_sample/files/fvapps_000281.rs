// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn flip_lights_spec(n: nat, m: nat) -> nat
    decreases m
{
    if n == 0 {
        0
    } else if m == 0 {
        1
    } else {
        // Simplified specification for demo
        if n <= 4 { (1u32 << (n as u32)) as nat } else { 16 }
    }
}
// </vc-helpers>

// <vc-spec>
fn flip_lights(n: nat, m: nat) -> (result: nat)
    requires n > 0,
    ensures 
        1 <= result && result <= (if n <= 4 { (1u32 << (n as u32)) } else { 16 }) as nat,
        (m == 0) ==> (result == 1),
        flip_lights_spec(n, 1000) == flip_lights_spec(n, 1001)
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
    // let test1 = flip_lights(1, 1);
    // assert(test1 == 2);
    // 
    // let test2 = flip_lights(2, 1);
    // assert(test2 == 3);
    // 
    // let test3 = flip_lights(3, 1);
    // assert(test3 == 4);
}