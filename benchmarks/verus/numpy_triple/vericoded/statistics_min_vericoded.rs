// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simple min for i8 */
fn min_i8(a: i8, b: i8) -> (result: i8)
    ensures
        result as int <= a as int,
        result as int <= b as int,
{
    if a <= b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn min(a: Vec<i8>) -> (result: i8)
    requires a.len() > 0,
    ensures
        exists|i: int| 0 <= i < a@.len() && a@[i] == result as int,
        forall|i: int| 0 <= i < a@.len() ==> result as int <= a@[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): implement min over vector using loop and invariants */
    let mut i: usize = 1usize;
    let mut m: i8 = a[0];
    proof {
        assert(m as int == a@[0]);
        assert(exists|j: int| 0 <= j < 1 && a@[j] == m as int);
    }
    while i < a.len()
        invariant
            1usize <= i && i <= a.len(),
            exists|j: int| 0 <= j < i as int && a@[j] == m as int,
            forall|j: int| 0 <= j < i as int ==> m as int <= a@[j],
        decreases a.len() - i
    {
        let old_m = m;
        let x: i8 = a[i];
        if x < m {
            m = x;
        }
        proof {
            if x < old_m {
                assert(m as int == a@[i as int]);
                assert(exists|j: int| 0 <= j < (i + 1) as int && a@[j] == m as int);
                assert(forall|j: int| 0 <= j < i as int ==> old_m as int <= a@[j]);
                assert(forall|j: int| 0 <= j < i as int ==> m as int <= a@[j]);
                assert(forall|j: int| 0 <= j < (i + 1) as int ==> m as int <= a@[j]);
            } else {
                assert(exists|j: int| 0 <= j < i as int && a@[j] == old_m as int);
                assert(exists|j: int| 0 <= j < (i + 1) as int && a@[j] == m as int);
                assert(forall|j: int| 0 <= j < (i + 1) as int ==> m as int <= a@[j]);
            }
        }
        i += 1;
    }
    proof {
        assert(i == a.len());
        assert(exists|j: int| 0 <= j < a@.len() && a@[j] == m as int);
        assert(forall|j: int| 0 <= j < a@.len() ==> m as int <= a@[j]);
    }
    m
}
// </vc-code>


}
fn main() {}