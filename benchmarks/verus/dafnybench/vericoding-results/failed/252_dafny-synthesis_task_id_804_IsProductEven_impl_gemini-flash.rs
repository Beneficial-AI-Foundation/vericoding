use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

// <vc-helpers>
fn is_product_even_helper(a: &[int], idx: nat) -> (result: bool)
    requires idx <= a.len()
    ensures result == (exists|i: int| 0 <= i < idx as int && is_even(a@[i]))
{
    if idx == 0 {
        false
    } else {
        proof {
            assert(is_product_even_helper(a, (idx - 1) as nat) == (exists|i: int| 0 <= i < (idx - 1) as int && is_even(a@[i])));
        }
        if is_even(a@[(idx - 1)]) {
            true
        } else {
            is_product_even_helper(a, (idx - 1) as nat)
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn is_product_even(a: &[int]) -> (result: bool)
    ensures result <==> exists|i: int| 0 <= i < a.len() && is_even(a@[i])
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut found_even: bool = false;
    let mut i: nat = 0;

    while i < n
        invariant
            0 <= i as int <= n as int,
            found_even <==> (exists|j: int| 0 <= j < i as int && is_even(a@[j]))
    {
        if is_even(a@[i]) {
            found_even = true;
            break;
        }
        i = i + 1;
    }
    
    found_even
}
// </vc-code>

fn main() {
}

}