use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &[i32]) -> (even_list: Vec<i32>)
    // All numbers in the output are even and exist in the input 
    ensures forall|i: int| 0 <= i < even_list.len() ==> is_even(even_list[i] as int) && exists|j: int| 0 <= j < arr.len() && arr[j] == even_list[i],
    // All even numbers in the input are in the output
    ensures forall|i: int| 0 <= i < arr.len() && is_even(arr[i] as int) ==> exists|j: int| 0 <= j < even_list.len() && even_list[j] == arr[i]
// </vc-spec>
// <vc-code>
{
    let mut even_list: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            // All numbers in even_list are even and from arr
            forall|k: int| 0 <= k < even_list.len() ==> 
                is_even(even_list[k] as int) && 
                exists|j: int| 0 <= j < arr.len() && #[trigger] arr[j] == even_list[k],
            // All even numbers from arr[0..i] are in even_list
            forall|k: int| 0 <= k < i && is_even(arr[k] as int) ==> 
                exists|j: int| 0 <= j < even_list.len() && #[trigger] even_list[j] == arr[k],
    {
        if arr[i] % 2 == 0 {
            assert(is_even(arr[i] as int));
            let old_len = even_list.len();
            even_list.push(arr[i]);
            
            assert(even_list[old_len as int] == arr[i as int]);
            assert(forall|k: int| 0 <= k < old_len ==> even_list[k] == even_list@[k]);
            
            // Prove that the new element preserves the invariants
            assert(is_even(even_list[old_len as int] as int));
            assert(exists|j: int| 0 <= j < arr.len() && arr[j] == even_list[old_len as int]) by {
                assert(arr[i as int] == even_list[old_len as int]);
            }
            
            // Prove that all even numbers from arr[0..i+1] are now in even_list
            assert(forall|k: int| 0 <= k <= i && is_even(arr[k] as int) ==> 
                exists|j: int| 0 <= j < even_list.len() && even_list[j] == arr[k]) by {
                assert(even_list[old_len as int] == arr[i as int]);
            }
        }
        i = i + 1;
    }
    
    even_list
}
// </vc-code>

fn main() {
}

}