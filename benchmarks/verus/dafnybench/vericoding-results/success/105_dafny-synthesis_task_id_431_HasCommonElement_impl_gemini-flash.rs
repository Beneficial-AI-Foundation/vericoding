use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier(external_body)]
#[inline(always)]
fn get_element_a(a: &[i32], i: usize) -> i32 {
    *a.get(i).unwrap()
}

#[verifier(external_body)]
#[inline(always)]
fn get_element_b(b: &[i32], j: usize) -> i32 {
    *b.get(j).unwrap()
}
// </vc-helpers>

// <vc-spec>
fn has_common_element(a: &[i32], b: &[i32]) -> (result: bool)
    ensures 
        result ==> (exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && a[i] == b[j]) &&
        (!result ==> (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> a[i] != b[j]))
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            forall |idx_a: int, idx_b: int|
                0 <= idx_a < i as int && 0 <= idx_b < b.len() as int ==> a[idx_a] != b[idx_b],
        decreases a.len() - i
    {
        let mut j: usize = 0;
        while j < b.len()
            invariant
                0 <= j && j <= b.len(),
                0 <= i && i < a.len(),
                forall |idx_b: int| 0 <= idx_b < j as int ==> a[i as int] != b[idx_b],
                forall |idx_a: int, idx_b: int|
                    0 <= idx_a < i as int && 0 <= idx_b < b.len() as int ==> a[idx_a] != b[idx_b],
            decreases b.len() - j
        {
            if a[i] == b[j] {
                // Proof for existence when true
                assert(exists|idx_a: int, idx_b: int| 0 <= idx_a < a.len() && 0 <= idx_b < b.len() && a[idx_a] == b[idx_b]) by {
                   assert(i < a.len() && j < b.len());  // Ensure indices are within bounds
                   assert(a[i as int] == b[j as int]);
                };
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    // Proof for non-existence when false
    assert(forall|idx_a: int, idx_b: int| 0 <= idx_a < a.len() && 0 <= idx_b < b.len() ==> a[idx_a] != b[idx_b]) by {
        assert(i == a.len()); // i has iterated through all of a
        assert(
            forall |idx_a: int, idx_b: int|
                0 <= idx_a < i as int && 0 <= idx_b < b.len() as int ==> a[idx_a] != b[idx_b]
        );
    };
    false
}
// </vc-code>

fn main() {}

}