// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert usize to int for use in specifications */
spec fn usize_to_int(u: usize) -> int {
    u as int
}

/* helper modified by LLM (iteration 5): monotonicity of usize_to_int for ordering proofs */
proof fn usize_to_int_ord(i: usize, j: usize)
    requires
        i < j,
    ensures
        usize_to_int(i) < usize_to_int(j),
{
    proof {
        assert(usize_to_int(i) < usize_to_int(j));
    }
}

/* helper modified by LLM (iteration 5): relate Vec length to Seq length */
proof fn vec_len_agree(a: &Vec<f32>)
    ensures
        usize_to_int(a.len()) == a@.len(),
{
    proof {
        assert(usize_to_int(a.len()) == a@.len());
    }
}

/* helper modified by LLM (iteration 5): relate Vec indexing to Seq indexing (proof) */
proof fn vec_index_agree(a: &Vec<f32>, i: usize)
    requires
        i < a.len(),
    ensures
        a[i] == a@[usize_to_int(i)],
{
    proof {
        assert(a[i] == a@[usize_to_int(i)]);
    }
}

/* helper modified by LLM (iteration 5): lemma that extending a prefix increases vec_sum by the new element */
proof fn vec_sum_snoc(a: Seq<f32>, n: int)
    requires
        0 <= n,
        n < a.len(),
    ensures
        vec_sum(a[0..n+1]) == vec_sum(a[0..n]) + a@[n],
{
    if n == 0 {
        proof {
            assert(vec_sum(a[0..1]) == a@[0] + vec_sum(a[1..]));
            assert(vec_sum(a[0..0]) == 0.0f32);
            assert(vec_sum(a[0..1]) == vec_sum(a[0..0]) + a@[0]);
        }
    } else {
        proof {
            assert(vec_sum(a[0..n+1]) == a@[0] + vec_sum(a[1..n+1]));
            assert(vec_sum(a[0..n]) == a@[0] + vec_sum(a[1..n]));
            vec_sum_snoc(a[1..], n - 1);
            assert(vec_sum(a[1..n+1]) == vec_sum(a[1..n]) + a[1..]@[n-1]);
            assert(a[1..]@[n-1] == a@[n]);
            assert(vec_sum(a[0..n+1]) == vec_sum(a[0..n]) + a@[n]);
        }
    }
}

// </vc-helpers>

// <vc-spec>
spec fn vec_sum(a: Seq<f32>) -> f32;

fn sum(a: Vec<f32>) -> (result: f32)
    ensures 
        result == vec_sum(a@),
        a.len() == 0 ==> result == 0.0f32,
        (forall|i: int| 0 <= i < a.len() ==> a[i] == 0.0f32) ==> result == 0.0f32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate with proofs to maintain prefix-sum invariant */
    let mut iu: usize = 0usize;
    let mut res: f32 = 0.0f32;
    while iu < a.len()
        invariant
            0 <= usize_to_int(iu),
            usize_to_int(iu) <= usize_to_int(a.len()),
            res == vec_sum(a@[0..usize_to_int(iu)]),
        decreases a.len() - iu
    {
        let v: f32 = a[iu];
        proof {
            vec_index_agree(&a, iu);
            vec_len_agree(&a);
            usize_to_int_ord(iu, a.len());
            vec_sum_snoc(a@, usize_to_int(iu));
            assert(res + a@[usize_to_int(iu)] == vec_sum(a@[0..(usize_to_int(iu) + 1)]));
        }
        res = res + v;
        iu = iu + 1usize;
    }
    res
}

// </vc-code>

}
fn main() {}