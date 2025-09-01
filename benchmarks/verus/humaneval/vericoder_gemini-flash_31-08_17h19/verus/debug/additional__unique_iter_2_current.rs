use vstd::prelude::*;

verus! {

// <vc-helpers>
fn is_unique(s: &Vec<i32>) -> bool {
    // Corrected index types to usize
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
    let mut i: usize = 0; // Changed type to usize

    while i < a.len()
        invariant
            0 <= i,
            i <= a.len(),
            result.len() <= (i + 1), // Removed casting for consistency
            is_unique(&result),
            forall|j: int| 0 <= j && (j as usize) < result.len() ==> exists|k: int| 0 <= k && (k as usize) < i && a[k as usize] == result[j as usize],
            forall|x: int, y: int| 0 <= x && (x as usize) < i && 0 <= y && (y as usize) < i && x < y ==> a[x as usize] <= a[y as usize],
            forall|j: int| 0 <= j && (j as usize) < result.len() ==> (result.len() == 1 ==> result[0] == a[0]),
            forall|j: int| 0 <= j && (j as usize)+1 < result.len() ==> result[j as usize] < result[(j as usize)+1],
            forall|k: int| 0 <= k && (k as usize) < i ==> {
                if (i as usize) < a.len() { // Add bounds check
                    a[k as usize] <= a[i as usize]
                } else {
                    true
                }
            },
            ({
                if result.len() > 0 {
                    let last_val_in_result = result.last().unwrap();
                    forall |k: int| 0 <= k && (k as usize) < i ==> a[k as usize] <= *last_val_in_result
                } else {
                    true
                }
            }),
            forall|x: int| 0 <= x && (x as usize) < i && result.contains(&a[x as usize])
    {
        let current_val = a[i];

        if result.len() == 0 {
            result.push(current_val);
        } else {
            let last_val_in_result = result.last().unwrap(); // Use .last().unwrap() correctly
            if current_val > *last_val_in_result {
                result.push(current_val);
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}
}