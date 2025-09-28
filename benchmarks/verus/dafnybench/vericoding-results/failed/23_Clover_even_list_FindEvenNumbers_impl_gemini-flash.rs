use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier(external_body)]
pub open spec fn contains_as_ref<T>(s: Seq<T>, t: T) -> bool {
    s.contains(t)
}
// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &[i32]) -> (even_numbers: Vec<i32>)
    ensures 
        (forall|x: i32| arr@.contains(x) && x % 2 == 0 ==> even_numbers@.contains(x)) &&
        (forall|x: i32| !arr@.contains(x) ==> !even_numbers@.contains(x)) &&
        (forall|k: int| 0 <= k < even_numbers@.len() ==> even_numbers@[k] % 2 == 0) &&
        (forall|k: int, l: int| 0 <= k < l < even_numbers@.len() ==> 
            exists|n: int, m: int| 0 <= n < m < arr@.len() && 
            #[trigger] even_numbers@[k] == #[trigger] arr@[n] && 
            #[trigger] even_numbers@[l] == #[trigger] arr@[m])
// </vc-spec>
// <vc-code>
{
    let mut even_numbers: Vec<i32> = Vec::new();
    let mut i: int = 0;

    #[verifier::loop_invariant(
        i <= arr.len(),
        // For any x in the processed part of arr (arr[0..i-1]), if x is even, it must be in even_numbers
        (forall|x: i32| (#[trigger] arr@.subsequence(0, i)).contains(x) && x % 2 == 0 ==> even_numbers@.contains(x)),
        // All elements in even_numbers are even
        (forall|k: int| 0 <= k < even_numbers@.len() ==> even_numbers@[k] % 2 == 0),
        // This invariant ensures the relative order and source of elements in even_numbers
        (forall|k: int, l: int| 0 <= k < l < even_numbers@.len() ==>
            exists|n: int, m: int| 0 <= n < m < i &&
            #[trigger] even_numbers@[k] == #[trigger] arr@[n] &&
            #[trigger] even_numbers@[l] == #[trigger] arr@[m])
    )]
    while i < arr.len()
    {
        let x = arr[i as usize];
        if x % 2 == 0 {
            even_numbers.push(x);
        }
        i = i + 1;
    }

    even_numbers
}
// </vc-code>

fn main() {
}

}