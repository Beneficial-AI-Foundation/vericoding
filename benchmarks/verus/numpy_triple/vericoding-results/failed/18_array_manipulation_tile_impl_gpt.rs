// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): modular arithmetic for (r*n + j) % n with 0 <= j < n */
proof fn lemma_mod_mul_add(n: int, r: int, j: int)
    requires
        n > 0,
        0 <= j < n
    ensures
        ((r * n + j) % n) == j
{
    assert(((r * n + j) % n) == j);
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
    /* code modified by LLM (iteration 4): maintain tiling invariant with nested loops and modular reasoning */
    let n_usize = a.len();
    let mut result: Vec<i32> = Vec::new();
    let mut r: usize = 0;
    while r < reps
        invariant
            a.len() == n_usize,
            n_usize > 0,
            r <= reps,
            (result.len() as int) == ((n_usize * r) as int),
            forall|k: int| 0 <= k < (result.len() as int) ==> result[k] == a[k % (n_usize as int)],
        decreases reps - r
    {
        let mut j: usize = 0;
        while j < n_usize
            invariant
                a.len() == n_usize,
                n_usize > 0,
                r <= reps,
                j <= n_usize,
                (result.len() as int) == ((n_usize * r + j) as int),
                forall|k: int| 0 <= k < (result.len() as int) ==> result[k] == a[k % (n_usize as int)],
            decreases n_usize - j
        {
            let prev_len: usize = result.len();
            let aj = a[j];
            result.push(aj);
            proof {
                let j_int: int = j as int;
                let r_int: int = r as int;
                let n: int = n_usize as int;
                assert(0 <= j_int && j_int < n);
                assert(n > 0);
                assert((prev_len as int) == ((n_usize as int) * r_int + j_int));
                lemma_mod_mul_add(n, r_int, j_int);
                assert(((prev_len as int) % n) == j_int);
                assert(j_int == j as int);
                assert(aj == a[j as int]);
                assert(a[j_int] == a[j as int]);
                assert(result[prev_len as int] == aj);
                assert(result[prev_len as int] == a[j_int]);
            }
            j = j + 1;
        }
        r = r + 1;
    }
    result
}
// </vc-code>

}
fn main() {}