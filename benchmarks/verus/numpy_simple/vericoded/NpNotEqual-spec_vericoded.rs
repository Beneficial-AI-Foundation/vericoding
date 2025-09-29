// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): equivalence between i8 inequality and int-cast inequality */
proof fn lemma_i8_int_neq_equiv(x: i8, y: i8)
    ensures
        (x as int != y as int) == (x != y),
{
    if x == y {
        assert(x as int == y as int);
    } else {
        assert(x != y);
        assert(x as int != y as int);
    }
}
// </vc-helpers>

// <vc-spec>
fn not_equal(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<bool>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == (a[i] as int != b[i] as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fix spec/exec indexing mix; reason via int index and seq view */
    let n = a.len();
    let mut res: Vec<bool> = Vec::new();
    while res.len() < n
        invariant
            a.len() == b.len(),
            res.len() <= n,
            n == a.len(),
            forall|j: int| 0 <= j < res.len() as int ==> res[j] == (a[j] as int != b[j] as int),
        decreases n as int - res.len() as int
    {
        let i = res.len();
        let xi: i8 = a[i];
        let yi: i8 = b[i];
        let val: bool = xi != yi;
        res.push(val);
        proof {
            let ii: int = i as int;
            assert(0 <= ii && ii < a.len() as int);
            assert(0 <= ii && ii < b.len() as int);
            let new_len: usize = res.len();
            assert(new_len == i + 1);
            let new_len_i: int = new_len as int;
            assert(ii == new_len_i - 1);
            assert(0 <= ii && ii < new_len_i);
            assert(res@[ii] == val);
            lemma_i8_int_neq_equiv(xi, yi);
            assert(val == (xi as int != yi as int));
            assert(xi == a@[ii]);
            assert(yi == b@[ii]);
            assert(res@[ii] == (a@[ii] as int != b@[ii] as int));
        }
    }
    res
}
// </vc-code>


}
fn main() {}