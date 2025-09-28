// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): basic properties of Seq::push for reasoning about vector views */
proof fn seq_push_props<T>(s: Seq<T>, x: T)
    ensures
        s.push(x).len() == s.len() + 1,
        s.push(x)@[s.len()] == x,
        forall|k: int| 0 <= k < s.len() ==> s.push(x)@[k] == s@[k],
{
}

/* helper modified by LLM (iteration 5): vec view length equals runtime length */
proof fn vec_len_view_eq<T>(v: Vec<T>)
    ensures
        v@.len() == v.len(),
{
}

/* helper modified by LLM (iteration 5): wrapping_sub equals spec subtraction for i8 */
proof fn wrapping_sub_spec_i8(a: i8, b: i8)
    ensures
        a.wrapping_sub(b) == a - b,
{
}
// </vc-helpers>

// <vc-spec>
fn subtract(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result@[i] == a@[i] - b@[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement element-wise subtraction with wrapping to avoid overflow and maintain invariant */
    let n = a.len();
    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            res.len() == i,
            i <= n,
            a.len() == n,
            b.len() == n,
            forall|k: int| 0 <= k < i ==> res@[k] == a@[k] - b@[k],
        decreases n - i
    {
        assert(i < a.len());
        assert(i < b.len());
        let ai = a[i];
        let bi = b[i];
        let di: i8 = ai.wrapping_sub(bi);
        res.push(di);
        proof {
            let ii: int = i as int;
            assert(a@[ii] == ai);
            assert(b@[ii] == bi);
            // After push, the newly added index equals the pushed value
            assert(res@[ii] == di);
            // Connect wrapping_sub with spec subtraction
            wrapping_sub_spec_i8(ai, bi);
            assert(di == ai - bi);
            assert(res@[ii] == a@[ii] - b@[ii]);
        }
        i = i + 1;
    }
    res
}
// </vc-code>


}
fn main() {}