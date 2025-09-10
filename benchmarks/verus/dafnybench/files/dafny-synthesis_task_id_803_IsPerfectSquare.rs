use vstd::prelude::*;

verus! {

fn is_perfect_square(n: int) -> (result: bool)
    requires 
        n >= 0,
    ensures 
        result == true ==> (exists|i: int| 0 <= i <= n && #[trigger] (i * i) == n),
        result == false ==> (forall|a: int| 0 < a*a < n ==> #[trigger] (a*a) != n),
{
    assume(false);
    unreached()
}

}
fn main() {}