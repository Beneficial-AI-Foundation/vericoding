// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simple int product spec for reasoning */
spec fn product_int(x: i32, y: i32) -> int { (x as int) * (y as int) }

/* helper modified by LLM (iteration 3): commutativity of integer multiplication */
proof fn product_commutative(x: i32, y: i32)
    ensures product_int(x, y) == product_int(y, x)
{ }
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_product(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i64>) by (nonlinear_arith)
    requires
        a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| #![auto] 0 <= i && i < a.len() ==> result[i] == (a[i] as i64) * (b[i] as i64),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): capture vector view as ghost before push to avoid spec-in-exec error; maintain loop invariant */
    let n = a.len();
    let mut r: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            a.len() == n,
            b.len() == n,
            i <= n,
            r.len() == i,
            forall|j: int| #![auto] 0 <= j && j < i as int ==> r[j] == (a[j] as i64) * (b[j] as i64)
        decreases n - i
    {
        let ai = a[i];
        let bi = b[i];
        let prod: i64 = (ai as i64) * (bi as i64);

        let old_len = r.len();
        let ghost r_old = r@;
        r.push(prod);
        assert(r.len() == old_len + 1);
        proof {
            assert(r@ == r_old.push(prod));
            assert(r[old_len as int] == prod);
            assert(forall|j: int| 0 <= j && j < old_len as int ==> r[j] == r_old[j]);
        }
        i += 1;
    }
    assert(i == n);
    assert(r.len() == a.len());
    assert(forall|j: int| 0 <= j && j < a.len() ==> r[j] == (a[j] as i64) * (b[j] as i64));
    r
}
// </vc-code>

}
fn main() {}