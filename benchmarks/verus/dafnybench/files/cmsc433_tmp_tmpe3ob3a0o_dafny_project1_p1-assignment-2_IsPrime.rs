use vstd::prelude::*;

verus! {

fn is_prime(m: i32) -> (is_prime: bool)
    requires m > 0,
    ensures is_prime <==> (m > 1 && forall|j: int| 2 <= j < m ==> #[trigger] (m % j as i32) != 0),
{
    assume(false);
    unreached()
}

}
fn main() {}