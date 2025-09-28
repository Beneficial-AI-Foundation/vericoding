use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

// <vc-helpers>
spec fn is_even(n: int) -> bool {
    n % 2 == 0
}
// </vc-helpers>

// <vc-spec>
fn is_product_even(a: &[int]) -> (result: bool)
    ensures result <==> exists|i: int| 0 <= i < a.len() && is_even(a@[i])
// </vc-spec>
// <vc-code>
{
    let mut found = false;
    let mut i: usize = 0;
    tracked mut i_int: int = 0;
    while i < a.len() && !found
        invariant
            i as int == i_int,
            0 <= i_int <= a.len() as int,
            found == (exists|j: int| #![trigger] is_even(a@[j]) && 0 <= j < i_int),
        decreases a.len() as int - i_int
    {
        if a[i] % 2 == 0 {
            found = true;
        }
        i += 1;
        proof {
            i_int = i_int + 1;
        }
    }
    found
}
// </vc-code>

fn main() {
}

}