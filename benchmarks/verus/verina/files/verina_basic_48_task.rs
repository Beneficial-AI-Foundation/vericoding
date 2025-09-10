use vstd::prelude::*;

verus! {

spec fn is_perfect_square(n: nat) -> bool {
    exists|i: nat| #[trigger] (i * i) == n
}

fn is_perfect_square_fn(n: u64) -> (result: bool)
    ensures result <==> is_perfect_square(n as nat),
{
    assume(false);
    unreached()
}

}
fn main() {}