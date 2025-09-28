// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed range iteration with an explicit loop and count in `count_nonzero_prime`. */
fn count_nonzero_prime(a: Seq<i8>) -> (res_count: usize)
    ensures
        res_count <= a.len(),
        a.len() == 0 ==> res_count == 0,
        (forall|i: int| 0 <= i < a.len() ==> a[i] == 0) ==> res_count == 0,
        (forall|i: int| 0 <= i < a.len() ==> a[i] != 0) ==> res_count == a.len(),
        (exists|i: int| 0 <= i < a.len() && a[i] != 0) ==> res_count > 0,
        (exists|i: int| 0 <= i < a.len() && a[i] == 0) ==> res_count < a.len(),
        res_count == ({ let mut count = 0; let mut k = 0; while k < a.len() { if a[k] != 0 { count = count + 1; } k = k + 1; } count }) as usize
{
    let mut count_val: usize = 0;
    let mut i: int = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            count_val == ({ let mut count = 0; let mut k = 0; while k < i { if a[k] != 0 { count = count + 1; } k = k + 1; } count }) as usize,
            count_val <= i as usize
        decreases a.len() - i
    {
        if a[i] != 0 { 
            count_val = count_val + 1;
        }
        i = i + 1;
    }
    count_val
}
// </vc-helpers>

// <vc-spec>
fn count_nonzero(a: Vec<i8>) -> (count: usize)
    ensures
        count <= a.len(),
        a.len() == 0 ==> count == 0,
        (forall|i: int| 0 <= i < a@.len() ==> a[i] == 0) ==> count == 0,
        (forall|i: int| 0 <= i < a@.len() ==> a[i] != 0) ==> count == a.len(),
        (exists|i: int| 0 <= i < a@.len() && a[i] != 0) ==> count > 0,
        (exists|i: int| 0 <= i < a@.len() && a[i] == 0) ==> count < a.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected `a.len()` to `a.len() as int` for integer comparison, fixed all compile errors including array indexing, and changed loop iteration from `Range<int>.filter` to an explicit loop inside the invariant for `res_count`. */
{
    let mut count: usize = 0;
    let mut i: usize = 0; 

    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            count == ({ let mut res_count = 0; let mut k = 0; while k < i { if a@[k] != 0 { res_count = res_count + 1; } k = k + 1; } res_count }) as usize,
            count <= i
        decreases (a.len() - i) as nat
    {
        if a@[i as int] != 0 {
            count = count + 1;
        }
        i = i + 1;
    }

    proof {
        assert(count == count_nonzero_prime(a@));
    }
    count
}
// </vc-code>

}
fn main() {}