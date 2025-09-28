// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no changes needed, kept existing helpers */
spec fn sum_of_products(s1: Seq<i32>, s2: Seq<i32>) -> int
    recommends s1.len() == s2.len(),
    decreases s1.len()
{
    if s1.len() == 0 {
        0
    } else {
        s1[0] * s2[0] + sum_of_products(s1.skip(1), s2.skip(1))
    }
}

/* helper modified by LLM (iteration 3): no changes needed, kept existing helpers */
proof fn lemma_sum_prod_snoc(s1: Seq<i32>, s2: Seq<i32>, x: i32, y: i32)
    requires s1.len() == s2.len(),
    ensures sum_of_products(s1.push(x), s2.push(y)) == sum_of_products(s1, s2) + x * y,
    decreases s1.len()
{
    if s1.len() > 0 {
        lemma_sum_prod_snoc(s1.skip(1), s2.skip(1), x, y);
    }
}

/* helper modified by LLM (iteration 3): no changes needed, kept existing helpers */
proof fn lemma_correlation_sum_equiv(a: Seq<i32>, v: Seq<i32>, k: int)
    requires
        v.len() <= a.len() - k,
    ensures
        correlation_sum(a, v, k) == sum_of_products(a.subrange(k, k + v.len()), v),
    decreases v.len()
{
    if v.len() > 0 {
        assert(a.subrange(k, k + v.len()).skip(1) == a.subrange(k + 1, k + v.len()));
        lemma_correlation_sum_equiv(a, v.skip(1), k + 1);
    }
}
// </vc-helpers>

// <vc-spec>
spec fn correlation_sum(a: Seq<i32>, v: Seq<i32>, k: int) -> int
    decreases v.len()
{
    if v.len() == 0 {
        0
    } else {
        a[k] * v[0] + correlation_sum(a, v.skip(1), k + 1)
    }
}

fn correlate(a: Vec<i32>, v: Vec<i32>) -> (result: Vec<i32>)
    requires 
        v.len() > 0,
        v.len() <= a.len(),
    ensures
        result.len() == a.len() + 1 - v.len(),
        forall|k: int| 0 <= k < result.len() ==> 
            result[k] == correlation_sum(a@, v@, k),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed compile error by using spec indexing in proof block */
    let mut result = Vec::new();
    let mut k: usize = 0;
    while k < a.len() + 1 - v.len()
        invariant
            v.len() <= a.len(),
            0 <= k <= a.len() + 1 - v.len(),
            result.len() == k,
            forall|j: int| 0 <= j < k ==> result@[j] == correlation_sum(a@, v@, j),
        decreases a.len() + 1 - v.len() - k
    {
        let mut current_sum: i32 = 0;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() <= a.len() - k,
                current_sum == sum_of_products(a@.subrange(k as int, k as int + i as int), v@.subrange(0, i as int)),
            decreases v.len() - i
        {
            proof {
                let k_int = k as int;
                let i_int = i as int;
                assert(a@.subrange(k_int, k_int + i_int + 1) == a@.subrange(k_int, k_int + i_int).push(a@[k_int + i_int]));
                assert(v@.subrange(0, i_int + 1) == v@.subrange(0, i_int).push(v@[i_int]));
                lemma_sum_prod_snoc(
                    a@.subrange(k_int, k_int + i_int),
                    v@.subrange(0, i_int),
                    a@[k_int + i_int],
                    v@[i_int]
                );
            }
            current_sum = current_sum + a[k + i] * v[i];
            i = i + 1;
        }

        proof {
            lemma_correlation_sum_equiv(a@, v@, k as int);
        }

        result.push(current_sum);
        k = k + 1;
    }
    result
}
// </vc-code>


}
fn main() {}