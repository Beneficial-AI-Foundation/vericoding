use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

// <vc-helpers>
fn is_even_exec(n: int) -> (result: bool)
    ensures result <==> is_even(n)
{
    n % 2 == 0
}
// </vc-helpers>

// <vc-spec>
fn is_product_even(a: &[int]) -> (result: bool)
    ensures result <==> exists|i: int| 0 <= i < a.len() && is_even(a@[i])
// </vc-spec>
// <vc-code>
{
    let mut i = 0;
    let mut found = false;
    while i < a.len() && !found
        invariant 0 <= i && i <= a.len()
        invariant found ==> exists |j: int| 0 <= j < i && is_even(a@[j])
        invariant !found ==> forall |j: int| 0 <= j < i ==> !is_even(a@[j])
    {
        if is_even_exec(a[i as int]) {
            found = true;
        }
        i += 1;
    }
    found
}
// </vc-code>

fn main() {
}

}