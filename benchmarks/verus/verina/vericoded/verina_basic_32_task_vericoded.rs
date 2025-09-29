// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): prove j < n from j <= n - 2 */
proof fn leq_implies_lt_from_minus_two(j: int, n: int)
    requires
        j <= n - 2,
    ensures
        j < n,
{
    assert(n - 2 < n);
}

// </vc-helpers>

// <vc-spec>
fn swap_first_and_last(a: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() > 0,
    ensures
        result.len() == a.len(),
        result[0] == a[a.len() - 1],
        result[result.len() - 1] == a[0],
        forall|i: int| 1 <= i < result.len() - 1 ==> result[i] == a[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed index bounds with explicit assertions and loop proof */
    let n = a.len();
    let mut res: Vec<i32> = Vec::new();
    assert(n == a.len());
    if n == 1 {
        assert(0 <= 0 && 0 < a.len() as int);
        res.push(a[0]);
        assert(res.len() == n);
        assert(0 <= (res.len() as int) - 1 && (res.len() as int) - 1 < res.len() as int);
        assert(res[0] == a[n - 1]);
        assert(res[(res.len() as int) - 1] == a[0]);
        res
    } else {
        assert(n as int == a.len() as int);
        assert(0 <= (n as int) - 1);
        assert(((n as int) - 1) < (a.len() as int));
        res.push(a[n - 1]);

        let mut j: usize = 1;
        while j <= n - 2
            invariant
                1 <= (j as int) <= (n as int) - 1,
                res.len() as int == j as int,
                res.len() >= 1,
                res[0] == a[(n as int) - 1],
                forall|k: int| 1 <= k < j as int ==> res[k] == a[k],
                n as int == a.len() as int,
            decreases (n as int) - (j as int)
        {
            proof { leq_implies_lt_from_minus_two(j as int, n as int); }
            assert(0 <= j as int);
            assert((j as int) < (n as int));
            assert((j as int) < (a.len() as int));
            res.push(a[j]);
            j += 1;
        }
        assert(0 <= 0 && 0 < a.len() as int);
        res.push(a[0]);

        assert(res.len() == n);
        assert(res[0] == a[(n as int) - 1]);
        assert(0 <= (res.len() as int) - 1 && (res.len() as int) - 1 < res.len() as int);
        assert(res[(res.len() as int) - 1] == a[0]);
        assert(forall|i: int| 1 <= i < (res.len() as int) - 1 ==> res[i] == a[i]);
        res
    }
}
// </vc-code>

}
fn main() {}