// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn all_nan(a: Seq<f32>) -> bool {
    forall|i: int| #![auto] 0 <= i < a.len() ==> (a[i] != a[i])
}

spec fn has_finite_value(a: Seq<f32>) -> bool {
    exists|i: int| #![auto] 0 <= i < a.len() && (a[i] == a[i])
}

fn nanmedian(a: Vec<f32>) -> (result: f32)
    ensures
        (all_nan(a@) ==> (result != result)) &&
        (has_finite_value(a@) ==> (result == result))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Use 0.0/0.0 to create NaN instead of f32::NAN */
    let mut finite_values = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < finite_values.len() ==> finite_values[j] == finite_values[j],
            forall|j: int| 0 <= j < i ==> (a[j] == a[j] ==> exists|k: int| 0 <= k < finite_values@.len() && finite_values@[k] == a[j]),
            forall|k: int| 0 <= k < finite_values@.len() ==> exists|j: int| 0 <= j < i && a[j] == finite_values@[k],
        decreases a.len() - i
    {
        if a[i] == a[i] {
            finite_values.push(a[i]);
        }
        i = i + 1;
    }
    
    if finite_values.len() == 0 {
        let nan = 0.0f32 / 0.0f32;
        proof {
            assert(forall|j: int| 0 <= j < a.len() ==> !(a[j] == a[j]));
            assert(forall|j: int| 0 <= j < a.len() ==> a[j] != a[j]);
            assert(all_nan(a@));
        }
        nan
    } else {
        proof {
            assert(finite_values@.len() > 0);
            assert(finite_values@[0] == finite_values@[0]);
            let witness_j = choose|j: int| 0 <= j < a.len() && a[j] == finite_values@[0];
            assert(0 <= witness_j < a.len());
            assert(a[witness_j] == a[witness_j]);
            assert(has_finite_value(a@));
        }
        finite_values[0]
    }
}
// </vc-code>

}
fn main() {}