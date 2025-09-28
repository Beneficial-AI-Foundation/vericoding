// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn f32_is_nan(x: f32) -> bool;
spec fn f32_le(a: f32, b: f32) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): runtime wrappers linking exec booleans to spec predicates */
fn rt_is_nan(x: f32) -> (res: bool)
    ensures
        res == f32_is_nan(x),
{
    x.is_nan()
}

/* helper modified by LLM (iteration 5): runtime wrapper for <= linking to spec comparator */
fn rt_le(a: f32, b: f32) -> (res: bool)
    ensures
        res == f32_le(a, b),
{
    if a.is_nan() || b.is_nan() { false } else { a <= b }
}

/* helper modified by LLM (iteration 5): lemma about casting usize bounds to int bounds */
proof fn lemma_usize_to_int_range(u: usize, n: usize)
    requires
        u < n,
    ensures
        0 <= (u as int) && (u as int) < (n as int),
{
}

// </vc-helpers>

// <vc-spec>
fn nanargmin(a: Vec<f32>) -> (result: usize)
    requires 
        a.len() > 0,
        exists|i: int| 0 <= i < a.len() && !f32_is_nan(a[i]),
    ensures
        result < a.len(),
        !f32_is_nan(a[result as int]),
        forall|j: int| 0 <= j < a.len() && !f32_is_nan(a[j]) ==> f32_le(a[result as int], a[j]),
        forall|j: int| 0 <= j < a.len() && !f32_is_nan(a[j]) && f32_le(a[j], a[result as int]) && f32_le(a[result as int], a[j]) ==> result as int <= j,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): forward scan with ghost witness and tie-breaking, using spec-linked runtime helpers */
    let n: usize = a.len();
    let mut i: usize = 0;
    let mut found: bool = false;
    let mut best: usize = 0;
    let ghost w: int = choose|j: int| 0 <= j && j < (n as int) && !f32_is_nan(a[j]);

    while i < n
        invariant
            0 <= (i as int),
            i <= n,
            0 <= w,
            w < (n as int),
            (!found) ==> (i as int) <= w,
            (!found) ==> forall|j: int| 0 <= j && j < (i as int) ==> f32_is_nan(a[j]),
            found ==> best < i,
            found ==> !f32_is_nan(a[best as int]),
            found ==> forall|j: int|
                0 <= j && j < (i as int) && !f32_is_nan(a[j]) ==> f32_le(a[best as int], a[j]),
            found ==> forall|j: int|
                0 <= j && j < (i as int) && !f32_is_nan(a[j]) && f32_le(a[j], a[best as int]) && f32_le(a[best as int], a[j]) ==> (best as int) <= j,
        decreases n - i
    {
        let is_nan_i = rt_is_nan(a[i]);
        proof { assert(is_nan_i == f32_is_nan(a[i as int])); }
        if !is_nan_i {
            if !found {
                best = i;
                found = true;
            } else {
                let le_i_best = rt_le(a[i], a[best]);
                let le_best_i = rt_le(a[best], a[i]);
                proof {
                    assert(le_i_best == f32_le(a[i as int], a[best as int]));
                    assert(le_best_i == f32_le(a[best as int], a[i as int]));
                }
                if le_i_best && !le_best_i {
                    best = i;
                }
            }
        }
        i = i + 1;
    }
    proof {
        assert(found);
    }
    best
}
// </vc-code>

}
fn main() {}