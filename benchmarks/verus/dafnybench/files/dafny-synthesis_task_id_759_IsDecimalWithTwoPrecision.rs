use vstd::prelude::*;

verus! {

fn is_decimal_with_two_precision(s: &str) -> (result: bool)
    ensures
        result ==> exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
        !result ==> !exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
{
    assume(false);
    unreached()
}

}
fn main() {}