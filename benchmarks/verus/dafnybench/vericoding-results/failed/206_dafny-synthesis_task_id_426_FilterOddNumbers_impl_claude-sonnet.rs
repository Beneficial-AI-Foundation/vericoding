use vstd::prelude::*;

verus! {

/**
 * Filter odd numbers from an array of numbers
 **/

spec fn is_odd(n: int) -> bool {
    n % 2 != 0
}

// <vc-helpers>
// Helper lemma to prove properties about filtered elements
proof fn lemma_filter_preserves_contains(arr: Seq<int>, filtered: Seq<int>, x: int)
    requires
        forall|i: int| 0 <= i < filtered.len() ==> arr.contains(filtered[i]),
        filtered.contains(x)
    ensures
        arr.contains(x)
{
    let idx = choose|i: int| 0 <= i < filtered.len() && filtered[i] == x;
    assert(arr.contains(filtered[idx]));
}

// Helper function to check if a number is odd in exec mode
fn is_odd_exec(n: int) -> (result: bool)
    ensures result == is_odd(n)
{
    n % 2int != 0int
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
    let mut odd_list = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            // All numbers in odd_list so far are odd and from arr
            forall|j: int| 0 <= j < odd_list.len() ==> is_odd(odd_list[j]) && arr@.contains(odd_list[j]),
            // All odd numbers processed so far are in odd_list
            forall|j: int| 0 <= j < i && is_odd(arr[j]) ==> odd_list@.contains(arr[j]),
    {
        if is_odd_exec(arr[i]) {
            odd_list.push(arr[i]);
        }
        i += 1;
    }
    
    odd_list
}
// </vc-code>

fn main() {}

}