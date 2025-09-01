use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn unique_better(a: &[i32]) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        forall|i: int, j: int|
            #![trigger a[i], a[j]]
            0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int, j: int|
            #![trigger result[i], result[j]]
            0 <= i && i < j && j < result.len() ==> result[i] < result[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut result = Vec::new();
    if a.len() == 0 {
        return result;
    }
    result.push(a[0]);

    let mut index = 1;
    while index < a.len()
        invariant
            1 <= index && index <= a.len(),
            // result is strictly increasing up to its current length
            forall|i: int, j: int|
                #![trigger result[i], result[j]]
                0 <= i && i < j && j < result.len() ==> result[i] < result[j],
            // each element in result is equal to some a[k] for k < index
            forall|k: int| #![trigger result[k]] 0 <= k && k < result.len() ==> exists|m: int| 0 <= m && m < index && a[m] == result[k],
            // the sequence in result corresponds to unique elements in order from a
            forall|k: int| #![trigger result[k]] 0 <= k && k < result.len() ==> 
                if k == 0 { 
                    exists|m: int| 0 <= m && m < index && a[m] == result[k] 
                } else { 
                    exists|m: int| 0 <= m && m < index && a[m] == result[k] && 
                    result[k] != result[k-1]
                },
        decreases (a.len() as nat) - (index as nat)
    {
        if a[index] != a[index - 1] {
            result.push(a[index]);
        }
        index += 1;
    }

    // Assert the post-condition holds
    assert(forall|i: int, j: int|
        #![trigger result[i], result[j]]
        0 <= i && i < j && j < result.len() ==> result[i] < result[j]);

    result
    // impl-end
}
// </vc-code>

fn main() {}
}