// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn all(a: Vec<f32>) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < a.len() ==> a[i] != 0.0f32),
        (a.len() == 0 ==> result == true),
        ((exists|i: int| 0 <= i < a.len() && a[i] == 0.0f32) ==> result == false),
        ((forall|i: int| 0 <= i < a.len() ==> a[i] != 0.0f32) ==> result == true),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix invariant preservation by checking before increment */
    let mut i: usize = 0;
    let mut found_zero = false;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            !found_zero ==> (forall|j: int| 0 <= j < i ==> a[j] != 0.0f32),
            found_zero ==> (exists|j: int| 0 <= j < i && a[j] == 0.0f32),
        decreases
            a.len() - i,
    {
        if a[i] == 0.0f32 {
            found_zero = true;
            assert(exists|j: int| 0 <= j <= i && a[j] == 0.0f32);
            return false;
        }
        assert(a[i] != 0.0f32);
        i = i + 1;
    }
    assert(i == a.len());
    assert(!found_zero);
    assert(forall|j: int| 0 <= j < a.len() ==> a[j] != 0.0f32);
    true
}
// </vc-code>

}
fn main() {}