use vstd::prelude::*;

verus! {

spec fn compare_precond(a: int, b: int) -> bool {
    true
}

spec fn compare_postcond(a: int, b: int, result: bool) -> bool {
    (a == b ==> result == true) && (a != b ==> result == false)
}

fn compare(a: int, b: int) -> (result: bool)
    requires compare_precond(a, b)
    ensures compare_postcond(a, b, result)
{
    if a == b {
        true
    } else {
        false
    }
}

}

fn main() {
    // Empty main function for compilation
}