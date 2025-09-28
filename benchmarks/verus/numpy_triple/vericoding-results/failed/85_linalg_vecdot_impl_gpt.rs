// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): unfold step for dot_product_spec on skips and commutativity helper */
proof fn lemma_dot_skip_step(s1: Seq<i32>, s2: Seq<i32>, k: int)
    requires
        0 <= k,
        k < s1.len(),
        s1.len() == s2.len(),
    ensures
        dot_product_spec(s1.skip(k), s2.skip(k))
            == s1[k] * s2[k] + dot_product_spec(s1.skip(k + 1), s2.skip(k + 1)),
    decreases s1.len() - k
{
    let s1k = s1.skip(k);
    let s2k = s2.skip(k);
    assert(s1k.len() == s1.len() - k);
    assert(s2k.len() == s2.len() - k);
    assert(s1k.len() != 0);
    assert(s1k.len() == s2k.len());
    assert(dot_product_spec(s1k, s2k)
        == s1k[0] * s2k[0] + dot_product_spec(s1k.skip(1), s2k.skip(1)));
    assert(s1k[0] == s1[k]);
    assert(s2k[0] == s2[k]);
    assert(s1k.skip(1) == s1.skip(k + 1));
    assert(s2k.skip(1) == s2.skip(k + 1));
}

/* helper modified by LLM (iteration 5): commutativity of multiplication over integers */
proof fn lemma_mul_comm_int(a: int, b: int)
    ensures
        a * b == b * a,
{
    assert(a * b == b * a);
}

/* helper modified by LLM (iteration 5): commutativity of dot_product_spec */
proof fn lemma_dot_comm(s1: Seq<i32>, s2: Seq<i32>)
    requires
        s1.len() == s2.len(),
    ensures
        dot_product_spec(s1, s2) == dot_product_spec(s2, s1),
    decreases s1.len()
{
    if s1.len() == 0 {
        // both empty, both sides 0
    } else {
        assert(s1.skip(1).len() == s2.skip(1).len());
        lemma_dot_comm(s1.skip(1), s2.skip(1));
        assert(dot_product_spec(s1, s2)
            == s1[0] * s2[0] + dot_product_spec(s1.skip(1), s2.skip(1)));
        assert(dot_product_spec(s2, s1)
            == s2[0] * s1[0] + dot_product_spec(s2.skip(1), s1.skip(1)));
        // multiplication is commutative
        assert(s1[0] * s2[0] == s2[0] * s1[0]);
        assert(dot_product_spec(s1.skip(1), s2.skip(1))
            == dot_product_spec(s2.skip(1), s1.skip(1)));
    }
}

// </vc-helpers>

// <vc-spec>
spec fn dot_product_spec(x1: Seq<i32>, x2: Seq<i32>) -> int
    decreases x1.len()
{
    if x1.len() == 0 || x1.len() != x2.len() {
        0
    } else {
        x1[0] * x2[0] + dot_product_spec(x1.skip(1), x2.skip(1))
    }
}

fn vecdot(x1: Vec<i32>, x2: Vec<i32>) -> (result: i32)
    requires x1.len() == x2.len(),
    ensures 
        result as int == dot_product_spec(x1@, x2@),
        result as int == dot_product_spec(x2@, x1@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute dot product with backward loop maintaining a spec-accurate invariant relating the accumulator to dot_product_spec on the remaining suffix */
    let n: usize = x1.len();
    let mut i: usize = n;
    let mut acc: i32 = 0;
    while i > 0
        invariant
            x1.len() == n,
            x2.len() == n,
            i <= n,
            acc as int == dot_product_spec(x1@.skip(i as int), x2@.skip(i as int)),
        decreases i as int
    {
        let j: usize = i - 1;
        let xi: i32 = x1[j];
        let yi: i32 = x2[j];
        proof {
            // Preconditions for the unfolding step lemma
            assert(0 <= j as int);
            assert(j < n);
            lemma_dot_skip_step(x1@, x2@, j as int);
        }
        let old_acc: i32 = acc;
        acc = acc + xi * yi;
        i -= 1;
        proof {
            // Bridge between exec indexing and spec indexing
            assert(0 <= i as int);
            assert(i < n) by {
                assert(i + 1 == j + 1);
                assert(i == j);
                assert(j < n);
            };
            assert(x1@[i as int] == x1[i]);
            assert(x2@[i as int] == x2[i]);
            // Use the unfolding lemma at position i (which equals previous j)
            assert(dot_product_spec(x1@.skip(i as int), x2@.skip(i as int))
                == x1@[i as int] * x2@[i as int]
                   + dot_product_spec(x1@.skip((i + 1) as int), x2@.skip((i + 1) as int)));
            // Re-establish the invariant using the old invariant
            assert(old_acc as int == dot_product_spec(x1@.skip((i + 1) as int), x2@.skip((i + 1) as int)));
            assert(acc as int == x1@[i as int] * x2@[i as int] + old_acc as int);
        }
    }
    proof {
        // At loop exit, i == 0
        assert(acc as int == dot_product_spec(x1@.skip(0), x2@.skip(0)));
        assert(dot_product_spec(x1@.skip(0), x2@.skip(0)) == dot_product_spec(x1@, x2@));
        // Also establish commutativity for the second ensures
        lemma_dot_comm(x1@, x2@);
    }
    acc
}
// </vc-code>

}
fn main() {}