use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn cal_div() -> (result: (i32, i32))
  ensures result.0 == 191i32 / 7i32 && result.1 == 191i32 % 7i32,
// </vc-spec>
// <vc-code>
{
    // Calculate 191 / 7 and 191 % 7
    let quotient: i32 = 27;
    let remainder: i32 = 2;
    
    // Verify our calculation
    assert(quotient * 7 + remainder == 191i32);
    assert(0 <= remainder && remainder < 7);
    assert(quotient == 191i32 / 7i32);
    assert(remainder == 191i32 % 7i32);
    
    (quotient, remainder)
}
// </vc-code>

fn main() {
}

}