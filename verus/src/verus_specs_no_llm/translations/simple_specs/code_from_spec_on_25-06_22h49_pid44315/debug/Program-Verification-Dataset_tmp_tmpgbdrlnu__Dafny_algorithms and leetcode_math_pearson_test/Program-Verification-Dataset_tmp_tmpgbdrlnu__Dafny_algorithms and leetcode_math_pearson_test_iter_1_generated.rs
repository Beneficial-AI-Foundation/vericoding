// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
    // Simple main function implementation
    // Since no specific requirements are given, we'll just return
}

spec fn isEven(x: nat) -> bool {
    x % 2 == 0
}

}