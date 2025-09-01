use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_product(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i64>) by (nonlinear_arith)
    // pre-conditions-start
    requires
        a.len() == b.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.len() == a.len(),
        forall|i: int| #![auto] 0 <= i && i < a.len() ==> result[i] == (a[i] as i64) * (b[i] as i64),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n: nat = a.len();
    assert(n == b.len());
    let mut res: Vec<i64> = Vec::new();
    let mut i: nat = 0;
    while i < n
        invariant { i <= n };
        invariant { res.len() == i };
        invariant { forall |j: nat| j < i ==> res@[j as int] == (a@[j as int] as i64) * (b@[j as int] as i64) };
        decreases { n - i };
    {
        let prod: i64 = (a@[i as int] as i64) * (b@[i as int] as i64);
        res.push(prod);
        assert(res.len() == i + 1);
        assert(res@[i as int] == prod);
        i = i + 1;
    }
    res
}
// </vc-code>

fn main() {}
}