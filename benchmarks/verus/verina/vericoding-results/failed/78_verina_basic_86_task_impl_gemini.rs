// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Unchanged from previous iteration. */
proof fn lemma_rotate_idx_equivalence(i: int, offset: int, n: int)
    requires
        n > 0,
        0 <= i < n,
        offset >= 0,
    ensures
        ((i as usize + (offset % n) as usize) % (n as usize)) as int == (i + offset) % n,
{
    let eff_offset = offset % n;
    vstd::arithmetic::div_mod::lemma_mod_range(offset, n);

    assert((i + offset) % n == (i + eff_offset) % n) by {
        vstd::arithmetic::div_mod::lemma_mod_add(i, offset, n);
        assert((i + offset) % n == (i % n + eff_offset) % n);
        assert(i % n == i);
    }

    assert(((i as usize + eff_offset as usize) % (n as usize)) as int == (i + eff_offset) % n)
        by(bit_vector);
}
// </vc-helpers>

// <vc-spec>
fn rotate(a: &Vec<i32>, offset: int) -> (result: Vec<i32>)
    requires offset >= 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            let src_idx = (i + offset) % (a.len() as int);
            #[trigger] result[i] == a[src_idx]
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed compilation error (comma) in while-loop invariant */
    let n = a.len();
    if n == 0 {
        return Vec::new();
    }

    let ghost n_int = n as int;

    proof {
        vstd::arithmetic::div_mod::lemma_mod_range(offset, n_int);
    }
    let effective_offset = (offset % n_int) as usize;

    let mut result = Vec::with_capacity(n);
    let mut i: usize = 0;

    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> {
                let src_idx_j = (j + offset) % n_int;
                (0 <= src_idx_j < n_int) && #[trigger] result[j] == a[src_idx_j]
            },
    {
        let src_idx = (i + effective_offset) % n;

        proof {
            let i_int = i as int;
            lemma_rotate_idx_equivalence(i_int, offset, n_int);
            assert(src_idx as int == (i_int + offset) % n_int);

            vstd::arithmetic::div_mod::lemma_mod_range(i_int + offset, n_int);
        }

        result.push(a[src_idx]);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}