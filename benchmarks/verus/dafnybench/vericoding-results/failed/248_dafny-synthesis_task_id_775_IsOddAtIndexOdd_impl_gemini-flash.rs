use vstd::prelude::*;

verus! {

spec fn is_odd(n: int) -> bool {
    n % 2 == 1
}

// <vc-helpers>
#[verifier(external_body)]
proof fn lemma_even_implies_not_odd(i: int)
    ensures !is_odd(i) <== i % 2 == 0
{}
// </vc-helpers>

// <vc-spec>
fn is_odd_at_index_odd(a: &[int]) -> (result: bool)
    ensures result <==> forall|i: int| 0 <= i < a.len() ==> (is_odd(i) ==> is_odd(a[i]))
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut res: bool = true;

    while i < a.len()
        invariant
            i <= a.len(),
            res <== (forall|k: int| 0 <= k < i as int ==> (is_odd(k) ==> is_odd(a[k as usize])))
    {
        if is_odd(i as int) {
            if !is_odd(a[i as usize]) {
                res = false;
            }
        } else {
            proof {
                lemma_even_implies_not_odd(i as int);
            }
        }
        i = i + 1;
    }
    res
}
// </vc-code>

fn main() {
}

}