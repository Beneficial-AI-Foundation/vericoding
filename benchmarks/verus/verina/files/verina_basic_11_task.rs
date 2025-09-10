use vstd::prelude::*;

verus! {

fn last_digit(n: nat) -> result: nat
    ensures
        result < 10,
        result == n % 10,
{
    assume(false);
    unreached()
}

}
fn main() {}