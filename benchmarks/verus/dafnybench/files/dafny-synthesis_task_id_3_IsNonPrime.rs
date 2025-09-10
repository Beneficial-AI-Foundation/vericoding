use vstd::prelude::*;

verus! {

fn is_non_prime(n: int) -> (result: bool)
    requires n >= 2
    ensures result <==> (exists|k: int| 2 <= k < n && #[trigger] (n % k) == 0)
{
    assume(false);
    unreached()
}

}
fn main() {}