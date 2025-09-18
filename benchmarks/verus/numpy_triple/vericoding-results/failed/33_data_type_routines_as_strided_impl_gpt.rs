// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): proves j < n from j + s <= n and s > 0 */
proof fn lemma_lt_from_add_pos_int(j: int, s: int, n: int)
    requires
        0 <= j,
        0 < s,
        j + s <= n,
    ensures
        j < n
{
    assert(s >= 1);
    assert(j + 1 <= j + s);
    assert(j + 1 <= n);
    assert(j < n);
}

/* helper modified by LLM (iteration 2): proves product positivity when factors are >=1 and >0 */
proof fn lemma_pos_of_product_ge_1(a: int, b: int)
    requires
        a >= 1,
        b > 0,
    ensures
        a * b > 0
{
    assert(b >= 1);
    assert(a >= 1);
    assert(a * b >= 1 * b);
    assert(1 * b >= 1 * 1);
    assert(1 * 1 == 1);
    assert(a * b >= 1);
    assert(a * b > 0);
}
// </vc-helpers>

// <vc-spec>
fn numpy_as_strided(x: &Vec<f32>, stride: usize, m: usize) -> (result: Vec<f32>)
    requires 
        stride > 0,
        m * stride <= x.len(),
    ensures
        result.len() == m,
        forall|i: int| 0 <= i < m ==> result[i] == x[i * stride],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implemented loop and fixed Seq indexing casts */
    let mut res: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;

    while i < m
        invariant
            stride > 0,
            i <= m,
            res.len() == i,
            j == i * stride,
            j + (m - i) * stride <= x.len(),
            forall|k: int| 0 <= k < i ==> res@[k] == x@[k * stride],
        decreases m - i
    {
        proof {
            let t: int = ((m - i) * stride) as int;
            assert(0 <= j as int);
            assert((m - i) as int >= 1);
            lemma_pos_of_product_ge_1((m - i) as int, stride as int);
            assert((j as int) + t <= x.len() as int);
            lemma_lt_from_add_pos_int(j as int, t, x.len() as int);
        }
        let xi = x[j];
        let ghost old_res: Seq<f32> = res@;
        let old_i: usize = i;
        let old_j: usize = j;
        res.push(xi);
        i += 1;
        j += stride;
        proof {
            assert(res@ == old_res.push(xi));
            assert(old_res.len() == old_i);
            assert(forall|k: int| 0 <= k < old_i ==> res@[k] == old_res[k]);
            assert(forall|k: int| 0 <= k < old_i ==> old_res[k] == x@[k * stride]);
            assert(forall|k: int| 0 <= k < old_i ==> res@[k] == x@[k * stride]);
            assert(res@[(old_i as int)] == xi);
            assert(old_j == old_i * stride);
            assert(res@[(old_i as int)] == x@[((old_i as int) * stride)]);
            assert(j + (m - i) * stride == old_j + (m - old_i) * stride);
            assert(j + (m - i) * stride <= x.len());
        }
    }
    res
}
// </vc-code>

}
fn main() {}