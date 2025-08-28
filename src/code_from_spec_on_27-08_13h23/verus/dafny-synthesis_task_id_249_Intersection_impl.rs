use vstd::prelude::*;

verus! {

// Predicate to check if an element exists in an array
spec fn in_array(a: &[i32], x: i32) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i as int] == x
}

// <vc-helpers>
// Helper spec function to check if a value exists in a Vec
spec fn vec_contains(v: Vec<i32>, x: i32) -> bool {
    exists|i: int| 0 <= i < v.len() && v@[i] == x
}

// Helper spec function to check if all elements in Vec are unique
spec fn vec_unique(v: Vec<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> v@[i] != v@[j]
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn intersection(a: &[i32], b: &[i32]) -> (result: Vec<i32>)
    ensures
        // All elements in the output are in both a and b
        forall|x: i32| result@.contains(x) ==> (in_array(a, x) && in_array(b, x)),
        // The elements in the output are all different
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j]
// </vc-spec>
// </vc-spec>

// <vc-code>
fn intersection(a: &[i32], b: &[i32]) -> (result: Vec<i32>)
    ensures
        // All elements in the output are in both a and b
        forall|x: i32| result@.contains(x) ==> (in_array(a, x) && in_array(b, x)),
        // The elements in the output are all different
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j]
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|x: i32| result@.contains(x) ==> (in_array(a, x) && in_array(b, x)),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l]
    {
        let x = a[i];
        let mut found_in_b = false;
        let mut j: usize = 0;

        while j < b.len()
            invariant
                0 <= j <= b.len(),
                found_in_b ==> in_array(b, x),
                !found_in_b ==> forall|k: int| 0 <= k < j ==> b[k as int] != x
        {
            if b[j] == x {
                found_in_b = true;
            }
            j = j + 1;
        }

        if found_in_b {
            let mut already_in_result = false;
            let mut k: usize = 0;

            while k < result.len()
                invariant
                    0 <= k <= result.len(),
                    already_in_result ==> result@.contains(x),
                    !already_in_result ==> forall|m: int| 0 <= m < k ==> result@[m] != x
            {
                if result[k] == x {
                    already_in_result = true;
                }
                k = k + 1;
            }

            if !already_in_result {
                result.push(x);
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}

}