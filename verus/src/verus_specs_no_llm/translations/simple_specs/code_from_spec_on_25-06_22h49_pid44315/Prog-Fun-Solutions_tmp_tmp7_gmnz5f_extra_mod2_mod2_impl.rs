use builtin::*;
use builtin_macros::*;

verus! {

spec fn f2(n: nat) -> nat {
    n % 2
}

fn main() {
}

fn mod2(n: u32) -> (a: u32)
    requires n < 0x80000000  // Ensure no overflow issues
    ensures
        a == f2(n as nat)
{
    let temp = n % 2;
    temp
}

}