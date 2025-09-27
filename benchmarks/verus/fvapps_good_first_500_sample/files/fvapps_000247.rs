// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs(n: int) -> int {
    if n < 0 { -n } else { n }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn clumsy(n: u32) -> (result: i32)
    requires n >= 1 && n <= 10000,
    ensures 
        n == 1 ==> result == 1,
        n == 2 ==> result == 2,
        n >= 3 && n <= 100 ==> (n as int) - 1 <= result && result <= (n as int) + 3
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
    // println!("{}", clumsy(4));
    // println!("{}", clumsy(10)); 
    // println!("{}", clumsy(1));
}