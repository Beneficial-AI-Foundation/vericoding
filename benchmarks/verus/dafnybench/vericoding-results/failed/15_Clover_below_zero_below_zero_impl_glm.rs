use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn below_zero(operations: Vec<i32>) -> (result: (Vec<i32>, bool))
    ensures
        result.0.len() == operations.len() + 1,
        result.0[0] == 0,
        forall|i: int| 0 <= i < (result.0.len() - 1) as int ==> result.0[i + 1] == result.0[i] + operations[i],
        result.1 == true ==> exists|i: int| 1 <= i <= operations.len() as int && result.0[i] < 0,
        result.1 == false ==> forall|i: int| 0 <= i < result.0.len() as int ==> result.0[i] >= 0,
// </vc-spec>
// <vc-code>
{
    let mut current: i32 = 0;
    let mut result_vec = Vec::new();
    result_vec.push(0);
    let mut found_neg = false;

    for i in 0..operations.len()
        invariant 
            result_vec@.len() == (i as int) + 1,
            result_vec@[0] == 0,
            forall|j: int| 0 <= j < (i as int) ==> result_vec@[j+1] == result_vec@[j] + operations@[j],
            current == result_vec@[i as int],
            found_neg ==> exists|j: int| 1 <= j <= (i as int) && (#[trigger] result_vec@[j]) < 0,
            forall|j: int| 
                1 <= j <= (i as int) 
                ==> (#[trigger] result_vec@[j]) >= 0 
                    || found_neg,
    {
        let next = current + operations[i];
        result_vec.push(next);
        if next < 0 {
            found_neg = true;
        }
        current = next;
    }

    (result_vec, found_neg)
}
// </vc-code>

fn main() {}

}