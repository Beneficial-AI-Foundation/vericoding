// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn array_product(a: &[i32], b: &[i32]) -> (c: Vec<i32>)
    requires 
        a.len() == b.len(),
    ensures 
        c.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] * b[i] == c[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): add explicit proof for loop invariant properties */
    let mut c: Vec<i32> = Vec::new();
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            a.len() == b.len(),
            n == a.len(),
            i <= n,
            c.len() == i,
            forall|j: int| 0 <= j < i as int ==> #[trigger] (a@[j] * b@[j]) == c@[j],
            forall|j: int| 0 <= j < i as int ==> i32::MIN <= a@[j] * b@[j] <= i32::MAX,
        decreases n - i,
    {
        proof {
            let product = (a@[i] as int) * (b@[i] as int);
            assert(i32::MIN <= product <= i32::MAX) by(nonlinear_arith) {}
            assert((a[i] * b[i]) as int == product) by(arith) requires i32::MIN <= product <= i32::MAX {}
        }

        let val = a[i] * b[i];
        c.push(val);

        assert(forall|j: int| 0 <= j < i as int ==> (a@[j] * b@[j]) == c@[j]) by {
            let c_old = old(c);
            assert(c.view().subrange(0, i as int) == c_old.view());
            forall|j: int| 0 <= j < i as int
            ensures (a@[j] * b@[j]) == c@[j]
            {
                assert((a@[j] * b@[j]) == c_old@[j]);
                assert(c@[j] == c_old@[j]);
            }
        };
        assert((a@[i] * b@[i]) == c@[i]);

        i = i + 1;
    }
    c
}
// </vc-code>

}
fn main() {}