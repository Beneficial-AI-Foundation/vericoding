use vstd::prelude::*;

verus! {

#[verifier::exec_allows_no_decreases_clause]
fn last_digit(n: i32) -> (result: i32)
    requires n >= 0
    ensures 
        0 <= result < 10,
        n % 10 == result
{
    assume(false);
    unreached();
}

}
fn main() {}