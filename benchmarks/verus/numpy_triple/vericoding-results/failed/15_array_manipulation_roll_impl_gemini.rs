// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [Fixed compilation errors and proof.] */
fn compute_normalized_index(i: usize, shift: i32, n: usize) -> (result: usize)
    requires
        0 < n,
    ensures
        result < n,
        result as int == normalize_index(i as int, shift as int, n as int),
{
    let i_i128 = i as i128;
    let shift_i128 = shift as i128;
    let n_i128 = n as i128;

    let src_idx_i128 = i_i128 - shift_i128;
    let result_i128 = src_idx_i128.rem_euclid(n_i128);

    proof {
        let i_int = i as int;
        let shift_int = shift as int;
        let n_int = n as int;
        let src_idx_int = i_int - shift_int;

        // The definition of `normalize_index` matches the definition of Euclidean remainder,
        // which is proven equivalent to `spec_rem_euclid` by broadcast lemmas in `vstd`.
        assert(normalize_index(i_int, shift_int, n_int) == src_idx_int.spec_rem_euclid(n_int));
        
        // The spec of the executable `rem_euclid` guarantees it computes `spec_rem_euclid`.
        assert(result_i128 as int == src_idx_int.spec_rem_euclid(n_int));
    }

    result_i128 as usize
}
// </vc-helpers>

// <vc-spec>
spec fn normalize_index(i: int, shift: int, n: int) -> int {
    let src_idx = i - shift;
    let mod_result = src_idx % n;
    if mod_result < 0 { mod_result + n } else { mod_result }
}

fn roll<T>(a: Vec<T>, shift: i32) -> (result: Vec<T>)
    ensures
        result.len() == a.len(),
        a.len() == 0 ==> result@ == a@,
        a.len() > 0 ==> forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i] == a[normalize_index(i, shift as int, a.len() as int)]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [No logic change, depends on fixed helper.] */
{
    let n = a.len();
    if n == 0 {
        return Vec::new();
    }

    let result = Vec::from_fn(n, |i: usize| {
        let index_to_get = compute_normalized_index(i, shift, n);
        a[index_to_get]
    });

    result
}
// </vc-code>


}
fn main() {}