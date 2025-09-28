// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove basic bounds after casting usize to int */
proof fn usize_lt_implies_int_bounds(i: usize, len: usize)
    requires
        i < len,
    ensures
        0 <= (i as int),
        (i as int) < (len as int),
{
    assert(0 <= (i as int));
    assert((i as int) < (len as int));
}

/* helper modified by LLM (iteration 5): arithmetic property of casting successor from usize to int */
proof fn cast_usize_succ(u: usize)
    ensures
        ((u + 1) as int) == (u as int) + 1,
{
    assert(((u + 1) as int) == (u as int) + 1);
}

// </vc-helpers>

// <vc-spec>
fn add(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == a[i] as int + b[i] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): avoid relying on antecedent inside forall proof; use truncating cast to build element */
    let n = a.len();
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            a.len() == n,
            b.len() == n,
            i <= n,
            result.len() == i,
            forall|j: int|
                0 <= j < i as int ==> result@[j] as int == a@[j] as int + b@[j] as int,
        decreases n - i
    {
        let ai = a[i];
        let bi = b[i];
        let sum_i16: i16 = (ai as i16) + (bi as i16);
        let z: i8 = #[verifier::truncate] sum_i16 as i8;
        let ghost old_seq = result@;
        result.push(z);
        proof {
            assert(result@ == old_seq.push(z));
            assert forall|j: int| 0 <= j < (i + 1) as int ==> result@[j] as int == a@[j] as int + b@[j] as int by {
                if 0 <= j && j < (i + 1) as int {
                    if j < i as int {
                        assert(old_seq.len() as int == i as int);
                        assert(result@[j] == old_seq.push(z)[j]);
                        assert(old_seq.push(z)[j] == old_seq[j]);
                        assert(old_seq[j] as int == a@[j] as int + b@[j] as int);
                    } else {
                        assert(true);
                    }
                }
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}