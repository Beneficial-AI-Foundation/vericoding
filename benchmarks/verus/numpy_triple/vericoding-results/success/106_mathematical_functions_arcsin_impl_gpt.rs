// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): spec mapping for discrete arcsin on {-1,0,1} with i32 results */
spec fn asin_i32(x: i32) -> i32 {
    if x == -1i32 {
        -2i32
    } else if x == 0i32 {
        0i32
    } else if x == 1i32 {
        2i32
    } else {
        0i32
    }
}

/* helper modified by LLM (iteration 2): executable arcsin consistent with spec and bounded range */
fn asin_exec(x: i32) -> (result: i32)
    ensures
        -2 <= result && result <= 2,
        (x == 0 ==> result == 0),
        (x == 1 ==> result == 2),
        (x == -1 ==> result == -2),
        result == asin_i32(x)
{
    if x == -1 {
        -2
    } else if x == 0 {
        0
    } else if x == 1 {
        2
    } else {
        0
    }
}

/* helper modified by LLM (iteration 2): monotonicity of the discrete asin on the domain [-1,1] */
proof fn asin_monotone(a: i32, b: i32)
    requires
        -1 <= a && a <= 1,
        -1 <= b && b <= 1,
        a <= b
    ensures
        asin_i32(a) <= asin_i32(b)
{
    if a == b {
        assert(asin_i32(a) == asin_i32(b));
    } else {
        if a == -1i32 {
            assert(asin_i32(a) == -2i32);
            if b == 0i32 {
                assert(asin_i32(b) == 0i32);
            } else {
                assert(b == 1i32);
                assert(asin_i32(b) == 2i32);
            }
        } else if a == 0i32 {
            assert(asin_i32(a) == 0i32);
            assert(b == 1i32);
            assert(asin_i32(b) == 2i32);
        } else {
            assert(a == 1i32);
            assert(b == 1i32);
            assert(asin_i32(a) == asin_i32(b));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn numpy_arcsin(x: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x.len() > 0,
        forall|i: int| 0 <= i < x.len() ==> -1 <= x[i as int] && x[i as int] <= 1,
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            -2 <= result[i] && result[i] <= 2 &&
            (x[i] == 0 ==> result[i] == 0) &&
            (x[i] == 1 ==> result[i] == 2) &&
            (x[i] == -1 ==> result[i] == -2)
        },
        forall|i: int, j: int| 0 <= i < x.len() && 0 <= j < x.len() && x[i] <= x[j] ==> result[i] <= result[j]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implement arcsin mapping with loop, invariants, and post-loop monotonicity proof */
    let n = x.len();
    let mut r: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == x.len(),
            r.len() == i,
            i <= n,
            forall|k: int| 0 <= k < i as int ==> {
                r@[k] == asin_i32(x[k]) &&
                -2 <= r@[k] && r@[k] <= 2 &&
                (x[k] == 0 ==> r@[k] == 0) &&
                (x[k] == 1 ==> r@[k] == 2) &&
                (x[k] == -1 ==> r@[k] == -2)
            }
        decreases n - i
    {
        let xi = x[i];
        let yi = asin_exec(xi);
        r.push(yi);
        i = i + 1;
    }
    proof {
        assert(i >= n);
        assert(i <= n);
        assert(i == n);
        assert forall|p: int, q: int|
            0 <= p < n && 0 <= q < n && x[p] <= x[q]
            implies r@[p] <= r@[q]
        by {
            if 0 <= p < n && 0 <= q < n && x[p] <= x[q] {
                assert(-1 <= x[p] && x[p] <= 1);
                assert(-1 <= x[q] && x[q] <= 1);
                asin_monotone(x[p], x[q]);
                assert(r@[p] == asin_i32(x[p]));
                assert(r@[q] == asin_i32(x[q]));
            }
        }
    }
    r
}
// </vc-code>

}
fn main() {}