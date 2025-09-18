// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix equiv_implies_equality proof to properly establish sequence equality */
proof fn equiv_implies_equality(a1: Vec<f32>, a2: Vec<f32>)
    requires
        a1.len() == a2.len(),
        forall|i: int| 0 <= i < a1.len() ==> a1[i] == a2[i]
    ensures
        a1 === a2
{
    let s1 = a1@;
    let s2 = a2@;
    assert(s1 =~= s2) by {
        assert(s1.len() == s2.len());
        assert forall|i: int| 0 <= i < s1.len() implies s1[i] == s2[i] by {
            assert(0 <= i < s1.len());
        };
    };
}

spec fn elems_equal_for_index(a1: Seq<f32>, a2: Seq<f32>, i: int) -> bool {
    a1[i] == a2[i]
}
// </vc-helpers>

// <vc-spec>
fn array_equiv(a1: Vec<f32>, a2: Vec<f32>) -> (result: bool)
    requires a1.len() == a2.len(),
    ensures result == (forall|i: int| 0 <= i < a1.len() ==> a1[i] == a2[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Add proper bounds verification and fix loop */
    let len = a1.len();
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            forall|j: int| 0 <= j < i ==> a1[j] == a2[j]
        decreases len - i
    {
        if a1[i] != a2[i] {
            return false;
        }
        i = i + 1;
    }
    proof {
        equiv_implies_equality(a1, a2);
    }
    true
}
// </vc-code>

}
fn main() {}