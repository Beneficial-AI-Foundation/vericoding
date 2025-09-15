// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 5): Fixed modulo operator to use `%` for positive numbers, replaced `verus_math::modulo` */
{
    let mut result: Vec<i32> = Vec::new();
    result.reserve(a.len());

    if a.len() == 0 {
        return result;
    }

    let len_usize = a.len();
    verus_proof! {
        assert(a.len() == (a.len() as int));
    }
    let ghost len_int: int = a.len() as int;
    let effective_offset = offset;

    let mut i: usize = 0;
    while i < len_usize
        invariant
            0 <= i as int <= len_int,
            result.len() == i,
            result.len() == (i as int),
            result.len() <= a.len(),
            // Proof that elements up to `i` have been correctly placed
            forall|j: int| 0 <= j < i as int ==> {
                let src_idx_int = (j + effective_offset) % len_int;
                #[trigger] result[j as usize] == a[src_idx_int as usize]
            },
            len_int == a.len() as int,
            len_usize == a.len(),
    {
        verus_proof! {
            // The `%` operator in Verus (and Rust for positive operands) behaves like mathematical modulo for positive numbers.
            // Given effective_offset >= 0, i >= 0, and len_int > 0, `i as int + effective_offset` is >= 0.
            // Therefore `(i as int + effective_offset) % len_int` will be in the range `[0, len_int - 1]`.
        }
        let ghost src_idx_int_ghost = (i as int + effective_offset) % len_int;
        assert(0 <= src_idx_int_ghost && src_idx_int_ghost < len_int);

        let src_idx_usize = src_idx_int_ghost as usize;
        result.push(a[src_idx_usize]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}