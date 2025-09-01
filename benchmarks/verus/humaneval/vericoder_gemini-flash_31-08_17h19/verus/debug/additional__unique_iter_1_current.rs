use vstd::prelude::*;

verus! {

// <vc-helpers>
fn is_unique(s: &Vec<i32>) -> bool {
    forall|i: int, j: int| 0 <= i && i < j && j < s.len() ==> s[i] < s[j]
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
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: int = 0;

    while i < a.len()
        invariant
            0 <= i,
            i <= a.len(),
            result.len() <= i + 1,
            is_unique(&result),
            forall|j: int| 0 <= j && j < result.len() ==> exists|k: int| 0 <= k && k < i && a[k] == result[j],
            forall|x: int, y: int| 0 <= x && x < i && 0 <= y && y < i && x < y ==> a[x] <= a[y],
            forall|j: int| 0 <= j && j < result.len() ==> (result.len() == 1 ==> result[0] == a[0]),
            forall|j: int| 0 <= j && j+1 < result.len() ==> result[j] < result[j+1],
            forall|k: int| 0 <= k && k < i ==> a[k] <= a[i],
            ({
                if result.len() > 0 {
                    let last_val_in_result = result@.last().unwrap();
                    forall |k: int| 0 <= k && k < i ==> a[k] <= last_val_in_result
                } else {
                    true
                }
            }),
            forall|x: int| 0 <= x && x < i && result.contains(&a[x])
    {
        let current_val = a[i];

        if result.len() == 0 {
            result.push(current_val);
        } else {
            let last_val_in_result = result@.last().unwrap();
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