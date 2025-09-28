use vstd::prelude::*;

verus! {

spec fn is_odd(n: int) -> bool {
    n % 2 == 1
}

// <vc-helpers>
// specification function is_odd is already defined in the PREAMBLE, so no need for additional helpers
// </vc-helpers>

// <vc-spec>
fn is_odd_at_index_odd(a: &[int]) -> (result: bool)
    ensures result <==> forall|i: int| 0 <= i < a.len() ==> (is_odd(i) ==> is_odd(a[i]))
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant forall|#[trigger] k: int| 0 <= k < (i as int) ==> (#[trigger] is_odd(k) ==> is_odd(a@[k]))
    {
        if is_odd(i as int) && !is_odd(a[i]) {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

fn main() {
}

}