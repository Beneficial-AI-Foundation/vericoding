// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate checking equality of main subrange and sub */
spec fn slices_equal(main: &Vec<i32>, k: int, sub: &Vec<i32>) -> bool {
    main@.subrange(k, k + (sub.len() as int)) =~= sub@
}
// </vc-helpers>

// <vc-spec>
fn is_sub_list(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)

    requires
        sub.len() <= main.len(),

    ensures
        result == (exists|k: int, l: int|
            0 <= k <= (main.len() - sub.len()) && l == k + sub.len() && (#[trigger] (main@.subrange(
                k,
                l,
            ))) =~= sub@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterative search with proofs for existence equivalence */
    let sub_len = sub.len();
    let mut result: bool = false;
    if sub_len == 0 {
        result = true;
        proof {
            assert(result == (exists|k: int, l: int|
                0 <= k <= (main.len() as int - (sub_len as int)) && l == k + (sub_len as int) && (main@.subrange(k, l) =~= sub@)
            ));
        }
        return result;
    }
    let max_start = main.len() - sub_len;
    let mut k: usize = 0;
    let mut pos: int = -1;
    while k <= max_start && !result
        invariant
            0 <= (k as int),
            (k as int) <= (max_start as int + 1),
            (forall|j: int| 0 <= j && j < (k as int) ==> !(main@.subrange(j, j + (sub_len as int)) =~= sub@)),
        decreases ((max_start as int + 1) - (k as int))
    {
        let mut i: usize = 0;
        let mut equal: bool = true;
        while i < sub_len
            invariant
                i <= sub_len,
            decreases ((sub_len as int) - (i as int))
        {
            if main[k + i] != sub[i] {
                equal = false;
                break;
            }
            i += 1;
        }
        if equal {
            result = true;
            pos = k as int;
        } else {
            k += 1;
        }
    }
    proof {
        if result {
            assert(0 <= pos && pos <= (max_start as int));
            assert(exists|kk: int, ll: int|
                kk == pos &&
                ll == pos + (sub_len as int) &&
                0 <= kk && kk <= (main.len() as int - (sub_len as int)) &&
                ll == kk + (sub_len as int) &&
                (main@.subrange(kk, ll) =~= sub@)
            );
            assert(result == (exists|k: int, l: int|
                0 <= k && k <= (main.len() as int - (sub_len as int)) &&
                l == k + (sub_len as int) &&
                (main@.subrange(k, l) =~= sub@)
            ));
        } else {
            let k_int = k as int;
            assert(k_int == (max_start as int + 1));
            assert(forall|j: int| 0 <= j && j < k_int ==> !(main@.subrange(j, j + (sub_len as int)) =~= sub@));
            assert(!(exists|kk: int, ll: int|
                0 <= kk && kk <= (main.len() as int - (sub_len as int)) &&
                ll == kk + (sub_len as int) &&
                (main@.subrange(kk, ll) =~= sub@)
            ));
            assert(result == (exists|k: int, l: int|
                0 <= k && k <= (main.len() as int - (sub_len as int)) &&
                l == k + (sub_len as int) &&
                (main@.subrange(k, l) =~= sub@)
            ));
        }
    }
    result
}
// </vc-code>

}
fn main() {}