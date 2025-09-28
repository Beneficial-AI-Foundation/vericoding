// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma that remainder is between 0 and n-1 for nonnegative j */
fn mod_bounds(n: int, j: int)
    requires
        n > 0,
        0 <= j,
    ensures
        0 <= j % n,
        j % n < n,
{
    proof {
        // Use integer division-remainder decomposition
        assert(j == (j / n) * n + j % n);
        assert(0 <= j % n);
        assert(j % n < n);
    }
}

/* helper modified by LLM (iteration 5): lemma that division of n*r by n yields r for nonnegative r */
fn mul_div_eq(n: int, r: int)
    requires
        n > 0,
        0 <= r,
    ensures
        (n * r) / n == r,
{
    proof {
        // For nonnegative r and positive n, (n*r)/n == r
        assert((n * r) / n == r);
    }
}

// </vc-helpers>

// <vc-spec>
fn tile(a: Vec<i32>, reps: usize) -> (result: Vec<i32>)
    requires 
        reps > 0,
        a.len() > 0,
    ensures
        result.len() == a.len() * reps,
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i % (a.len() as int)],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement tile using int counters and int indexing to match specs */
    let n: int = a.len();
    let reps_i: int = reps as int;
    let mut result: Vec<i32> = Vec::new();
    let mut r: int = 0;
    while r < reps_i
        invariant
            0 <= r,
            r <= reps_i,
            result.len() == r * n,
            forall|j: int| 0 <= j < result.len() ==> result[j] == a[j % n],
        decreases reps_i - r
    {
        let mut k: int = 0;
        while k < n
            invariant
                0 <= k,
                k <= n,
                result.len() == r * n + k,
                forall|j: int| 0 <= j < result.len() ==> result[j] == a[j % n],
            decreases n - k
        {
            result.push(a[k]);
            k += 1;
        }
        r += 1;
    }
    result
}

// </vc-code>

}
fn main() {}