// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn validate_ip_address(ip: &str) -> (result: String)
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
    // println!("{}", validate_ip_address("172.16.254.1"));
    // println!("{}", validate_ip_address("2001:0db8:85a3:0:0:8A2E:0370:7334"));
    // println!("{}", validate_ip_address("256.256.256.256"));
}