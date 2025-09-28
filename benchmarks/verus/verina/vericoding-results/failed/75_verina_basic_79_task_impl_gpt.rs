// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): witness existence of an index within a bound */
proof fn lemma_exists_index_in_range(w: usize, x: usize)
    requires
        w < x,
    ensures
        exists|i: int| 0 <= i && i < x && i == w as int
{
    assert(exists|i: int| 0 <= i && i < x && i == w as int) by {
        assert(0 <= w as int);
        assert(w < x);
    };
}

/* helper modified by LLM (iteration 5): witness existence of an index w < x with value m */
proof fn lemma_exists_value_at_w(a: &Vec<i32>, x: usize, w: usize, m: i32)
    requires
        w < x,
        w < a.len(),
        a[w as int] == m,
    ensures
        exists|i: int| 0 <= i && i < x && a[i] == m
{
    assert(exists|i: int| 0 <= i && i < x && a[i] == m) by {
        assert(0 <= w as int);
        assert(w < x);
        assert(a[w as int] == m);
    };
}
// </vc-helpers>

// <vc-spec>
fn online_max(a: &Vec<i32>, x: usize) -> (result: (i32, usize))
    requires
        a.len() > 0,
        x < a.len(),
    ensures
        ({
            let (m, p) = result;
            x <= p && p < a.len()
            && (forall|i: int| 0 <= i < x ==> a[i] <= m)
            && (exists|i: int| 0 <= i < x && a[i] == m)
            && ((p < a.len() - 1) ==> (exists|i: int| x <= i <= p && a[i] > m))
            && ((forall|i: int| x <= i < a.len() ==> a[i] <= m) ==> p == a.len() - 1)
        })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute prefix max up to x, then scan suffix to find first index > m; wrap proof lemma calls and fix indexing */
    let n = a.len();
    let mut m: i32 = a[0];
    let mut w: usize = 0;
    let mut k: usize = 0;
    while k < x
        invariant
            n == a.len(),
            k <= x,
            w < n,
            forall|i: int| 0 <= i < k ==> a[i] <= m,
            k == 0 || (w < k && a[w as int] == m),
        decreases x - k
    {
        assert(0 <= k as int && k < n);
        if a[k] > m {
            m = a[k];
            w = k;
        }
        k = k + 1;
    }

    assert(forall|i: int| 0 <= i < x ==> a[i] <= m);
    if x > 0 {
        assert(w < x);
        assert(w < n);
        assert(a[w as int] == m);
        proof { lemma_exists_value_at_w(a, x, w, m); }
    } else {
        proof { }
    }

    let mut p: usize = x;
    while p < n - 1 && { assert(0 <= p as int && p < n); a[p] <= m }
        invariant
            n == a.len(),
            x <= p && p < n,
            forall|i: int| x <= i < p ==> a[i] <= m,
        decreases (n - 1) - p
    {
        p = p + 1;
    }

    if p < n - 1 {
        assert(0 <= p as int && p < n);
        assert(a[p as int] > m);
        assert(exists|i: int| x <= i && i <= p && a[i] > m) by {
            assert(0 <= p as int);
            assert(x <= p);
            assert(a[p as int] > m);
        };
    }

    assert(((forall|i: int| x <= i && i < n ==> a[i] <= m)) ==> p == n - 1) by {
        if forall|i: int| x <= i && i < n ==> a[i] <= m {
            if p < n - 1 {
                assert(x <= p && p < n);
                assert(a[p as int] <= m);
                assert(a[p as int] > m);
            }
            assert(p >= n - 1);
            assert(p == n - 1) by { assert(p < n); }
        }
    };

    (m, p)
}
// </vc-code>

}
fn main() {}