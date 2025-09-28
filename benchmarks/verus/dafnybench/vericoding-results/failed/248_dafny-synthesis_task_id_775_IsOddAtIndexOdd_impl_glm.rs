use vstd::prelude::*;

verus! {

spec fn is_odd(n: int) -> bool {
    n % 2 == 1
}

// <vc-helpers>
// No helpers needed.
// </vc-helpers>

// <vc-spec>
fn is_odd_at_index_odd(a: &[int]) -> (result: bool)
    ensures result <==> forall|i: int| 0 <= i < a.len() ==> (is_odd(i) ==> is_odd(a[i]))
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    for i in 0..n
        invariant 
            forall|j: int| 0 <= j < (i as int) ==> (is_odd(j) ==> is_odd(a@[j]))
    {
        if is_odd(i as int) {
            if !is_odd(a[i]) {
                return false;
            }
        }
    }
    true
}
// </vc-code>

fn main() {
}

}