// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): fixed invalid trigger syntax in loop invariant */
    let mut even_numbers: Vec<i32> = Vec::new();
    let mut even_indices: Ghost<Seq<int>> = Ghost(Seq::empty());
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            even_numbers@.len() == even_indices@.len(),
            forall|k: int| 0 <= k < even_numbers@.len() ==> even_numbers@[k] % 2 == 0,
            forall|j: int| 0 <= j < (i as int) && arr@[j] % 2 == 0 ==> even_numbers@.contains(arr@[j]),
            forall|k: int| 0 <= k < even_indices@.len() ==> even_indices@[k] < (i as int),
            forall|k: int, l: int| 0 <= k < l < even_indices@.len() ==> even_indices@[k] < even_indices@[l],
            forall|k: int| 0 <= k < even_numbers@.len() ==> #[trigger] even_numbers@[k] == arr@[even_indices@[k]],
        decreases arr.len() - i
    {
        let element = arr[i];
        if element % 2 == 0 {
            even_numbers.push(element);
            even_indices = Ghost(even_indices@.push(i as int));
        }
        i = i + 1;
    }

    even_numbers
}
// </vc-code>

}
fn main() {}