use vstd::prelude::*;

verus! {

/**
 * Filter odd numbers from an array of numbers
 **/

spec fn is_odd(n: int) -> bool {
    n % 2 != 0
}

// <vc-helpers>
// Helper lemma to prove that if we've processed elements 0..i and found all odds up to that point,
// and we add an odd element at position i, we still have all odds up to i+1
proof fn lemma_extend_contains(arr: Seq<i32>, result: Seq<i32>, i: int)
    requires
        0 <= i < arr.len(),
        is_odd(arr[i] as int),
        forall|j: int| 0 <= j < i && is_odd(arr[j] as int) ==> result.contains(arr[j]),
    ensures
        forall|j: int| 0 <= j < i + 1 && is_odd(arr[j] as int) ==> result.push(arr[i]).contains(arr[j]),
{
    assert forall|j: int| 0 <= j < i + 1 && is_odd(arr[j] as int) implies result.push(arr[i]).contains(arr[j]) by {
        if j < i {
            assert(result.contains(arr[j]));
            assert(result.push(arr[i]).contains(arr[j]));
        } else {
            assert(j == i);
            assert(result.push(arr[i]).contains(arr[i]));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn filter_odd_numbers(arr: &[int]) -> (odd_list: Vec<int>)
    ensures 
        // All numbers in the output are odd and exist in the input 
        forall|i: int| 0 <= i < odd_list.len() ==> is_odd(odd_list[i]) && arr@.contains(odd_list[i]),
        // All odd numbers in the input are in the output
        forall|i: int| 0 <= i < arr.len() && is_odd(arr[i]) ==> odd_list@.contains(arr[i]),
// </vc-spec>
// <vc-code>
{
    let mut odd_list: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            // All elements in odd_list are odd and from arr
            forall|j: int| 0 <= j < odd_list.len() ==> 
                is_odd(#[trigger] odd_list[j] as int) && arr@.contains(odd_list[j]),
            // All odd elements from arr[0..i] are in odd_list
            forall|j: int| 0 <= j < i ==> 
                is_odd(arr[j] as int) ==> odd_list@.contains(arr[j]),
    {
        if arr[i] % 2 != 0 {
            let old_list = odd_list@;
            proof {
                lemma_extend_contains(arr@, old_list, i as int);
            }
            odd_list.push(arr[i]);
            
            assert(odd_list@.last() == arr[i as int]);
            assert(forall|j: int| 0 <= j < old_list.len() ==> odd_list[j] == old_list[j]);
        }
        i = i + 1;
    }
    
    odd_list
}
// </vc-code>

fn main() {}

}