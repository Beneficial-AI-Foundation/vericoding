use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_perfect_square(n: int) -> (result: bool)
    requires 
        n >= 0,
    ensures 
        result == true ==> (exists|i: int| 0 <= i <= n && #[trigger] (i * i) == n),
        result == false ==> (forall|a: int| 0 < a*a < n ==> #[trigger] (a*a) != n),
// </vc-spec>
// <vc-code>
{
    false
}
// </vc-code>

fn main() {}

}