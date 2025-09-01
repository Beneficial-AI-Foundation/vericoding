use vstd::prelude::*;

verus! {

// <vc-helpers>
fn is_unique(s: &Vec<i32>) -> bool {
    // Corrected index types to usize
    // The original predicate checks for strictly increasing sequence.
    // The postcondition for `unique` also checks for strictly increasing sequence.
    // So this helper function is correct as is.
    forall|i: int, j: int| 0 <= i && i < j && (j as usize) < s.len() ==> s[i as usize] < s[j as usize]
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn unique(a: &[i32]) -> (result: Vec<i32>)
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
#[verifier::loop_isolation(false)]
fn unique(a: &[i32]) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        forall|i: int, j: int|
            #![trigger a[i], a[j]]
            0 <= i && i < j && (j as usize) < a.len() ==> a[i as usize] <= a[j as usize],
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int, j: int|
            #![trigger result[i], result[j]]
            0 <= i && i < j && (j as usize) < result.len() ==> result[i as usize] < result[j as usize],
    // post-conditions-end
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    if a.len() == 0 {
        return result;
    }

    assert(a.len() > 0);

    result.push(a[0]);
    i = 1;

    while i < a.len()
        invariant
            0 < i,
            i <= a.len(),
            result.len() <= i,
            is_unique(&result),
            forall|x: int, y: int| 0 <= x && (x as usize) < i && 0 <= y && (y as usize) < i && x < y ==> a[x as usize] <= a[y as usize], // From precondition
            // All elements in result are from the original array `a`
            forall|j: int| 0 <= j && (j as usize) < result.len() ==> ({
                let found_idx: int = verus_model_cast_to_int(result[j as usize]);
                exists|k: int| 0 <= k && (k as usize) < i && a[k as usize] == found_idx
            }),
            // The last element of result is the maximum among the processed elements that are included in result
            ({
                if result.len() > 0 {
                    let last_val_in_result = result.last().unwrap();
                    forall |k: int| 0 <= k && (k as usize) < i ==> a[k as usize] <= *last_val_in_result || !result.contains(&a[k as usize])
                } else {
                    true
                }
            }),
            // All elements processed so far are less than or equal to the current last element of result IF they are in result.
            // If result.len() > 0, then a[0] == result[0].
            // If result.len() > 0 and 0 <= k < i, then a[k] <= result.last().unwrap()
            forall|k: int| 0 <= k && (k as usize) < i ==> ({
                if result.len() > 0 {
                    a[k as usize] <= *result.last().unwrap()
                } else {
                    true
                }
            })
    {
        let current_val = a[i];
        let last_val_in_result = result.last().unwrap();

        if current_val > *last_val_in_result {
            result.push(current_val);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}
}