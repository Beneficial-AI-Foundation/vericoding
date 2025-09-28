// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): base lemma stating empty product equals one */
proof fn poly_eval_empty_is_one(x_val: int)
    ensures
        poly_eval_at_point(x_val, Seq::<int>::empty()) == 1,
{
    assert(poly_eval_at_point(x_val, Seq::<int>::empty()) == 1);
}

/* helper modified by LLM (iteration 5): unfolding lemma for the tail of the sequence */
proof fn poly_eval_tail(x_val: int, roots: Seq<int>)
    requires
        roots.len() > 0,
    ensures
        poly_eval_at_point(x_val, roots)
            == (x_val - roots[0]) * poly_eval_at_point(x_val, roots.subrange(1, roots.len() as int)),
{
    assert(roots.len() > 0);
    assert(poly_eval_at_point(x_val, roots)
        == (x_val - roots[0]) * poly_eval_at_point(x_val, roots.subrange(1, roots.len() as int)));
}

/* helper modified by LLM (iteration 5): lemma for extending the product by one more root in the prefix */
proof fn poly_eval_prefix_mul_tail(x_val: int, roots: Seq<int>, k: int)
    requires
        0 <= k < roots.len(),
    ensures
        poly_eval_at_point(x_val, roots.subrange(0, k + 1))
            == poly_eval_at_point(x_val, roots.subrange(0, k)) * (x_val - roots[k]),
    decreases k
{
    if k == 0 {
        assert(roots.subrange(0, 1).len() == 1);
        assert(roots.subrange(0, 1)[0] == roots[0]);
        poly_eval_empty_is_one(x_val);
        assert(poly_eval_at_point(x_val, roots.subrange(0, 1))
            == (x_val - roots.subrange(0, 1)[0]) * poly_eval_at_point(x_val, Seq::<int>::empty()));
        assert(poly_eval_at_point(x_val, roots.subrange(0, 0)) == 1);
        assert(poly_eval_at_point(x_val, roots.subrange(0, 1))
            == poly_eval_at_point(x_val, roots.subrange(0, 0)) * (x_val - roots[0]));
    } else {
        let s = roots.subrange(1, k + 1);
        assert(s.len() == k);
        poly_eval_prefix_mul_tail(x_val, s, k - 1);
        proof {
            assert(poly_eval_at_point(x_val, roots.subrange(0, k + 1))
                == (x_val - roots[0]) * poly_eval_at_point(x_val, roots.subrange(1, k + 1)));
            assert(s[k - 1] == roots[k]);
            assert(poly_eval_at_point(x_val, roots.subrange(1, k + 1))
                == poly_eval_at_point(x_val, roots.subrange(1, k)) * (x_val - roots[k]));
            assert(poly_eval_at_point(x_val, roots.subrange(0, k))
                == (x_val - roots[0]) * poly_eval_at_point(x_val, roots.subrange(1, k)));
            assert(poly_eval_at_point(x_val, roots.subrange(0, k + 1))
                == poly_eval_at_point(x_val, roots.subrange(0, k)) * (x_val - roots[k]));
        }
    }
}
// </vc-helpers>

// <vc-spec>
spec fn poly_eval_at_point(x_val: int, roots: Seq<int>) -> int
    decreases roots.len()
{
    if roots.len() == 0 {
        1
    } else {
        (x_val - roots[0]) * poly_eval_at_point(x_val, roots.subrange(1, roots.len() as int))
    }
}

fn polyvalfromroots(x: Vec<i8>, r: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == poly_eval_at_point(x[i] as int, r@.map_values(|v: i8| v as int)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): remove conditional in proof block and maintain invariants */
    let n: usize = x.len();
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0usize;
    while i < n
        invariant
            0 <= i as int <= n as int,
            result.len() == i,
            forall|k: int| 0 <= k < i as int ==> result[k] as int == poly_eval_at_point(x[k] as int, r@.map_values(|v: i8| v as int)),
        decreases n as int - i as int
    {
        let xi: i8 = x[i];
        let mut j: usize = 0usize;
        let mut acc: i8 = 1i8;
        while j < r.len()
            invariant
                0 <= j as int <= r.len() as int,
                acc as int == poly_eval_at_point(xi as int, r@.map_values(|v: i8| v as int).subrange(0, j as int)),
            decreases r.len() as int - j as int
        {
            let factor: i8 = xi - r[j];
            proof {
                assert(0 <= j as int && j as int < r.len() as int);
                poly_eval_prefix_mul_tail(xi as int, r@.map_values(|v: i8| v as int), j as int);
            }
            acc = acc * factor;
            j = j + 1usize;
        }
        proof {
            assert(j as int == r.len() as int);
            assert(r@.map_values(|v: i8| v as int).subrange(0, r.len() as int) == r@.map_values(|v: i8| v as int));
        }
        result.push(acc);
        i = i + 1usize;
    }
    result
}
// </vc-code>

}
fn main() {}