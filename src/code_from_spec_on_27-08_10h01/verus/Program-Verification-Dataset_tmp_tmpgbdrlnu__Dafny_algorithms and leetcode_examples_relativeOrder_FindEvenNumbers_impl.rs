use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

// <vc-helpers>
spec fn all_even_from_prefix(arr: &[int], prefix_len: int, result: Seq<int>) -> bool {
    forall|i: int| 0 <= i < prefix_len && is_even(arr[i as usize]) ==> 
        result.contains(arr[i as usize])
}

spec fn all_from_arr_prefix(arr: &[int], prefix_len: int, result: Seq<int>) -> bool {
    forall|x: int| result.contains(x) ==> 
        exists|i: int| 0 <= i < prefix_len && arr[i as usize] == x
}

spec fn order_preserved_prefix(arr: &[int], prefix_len: int, result: Seq<int>) -> bool {
    forall|k: int, l: int| 0 <= k < l < result.len() ==>
        exists|n: int, m: int| 0 <= n < m < prefix_len && 
            result[k] == arr[n as usize] && 
            result[l] == arr[m as usize]
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn find_even_numbers(arr: &[int]) -> (even_numbers: Vec<int>)
    ensures
        // All even numbers from arr are in the result
        forall|i: int| 0 <= i < arr.len() && is_even(arr[i]) ==> 
            #[trigger] even_numbers@.contains(arr[i]),
        // All numbers in result come from arr  
        forall|x: int| #[trigger] even_numbers@.contains(x) ==> 
            exists|i: int| 0 <= i < arr.len() && arr[i] == x,
        // Order preservation property
        forall|k: int, l: int| 0 <= k < l < even_numbers.len() ==>
            exists|n: int, m: int| 0 <= n < m < arr.len() && 
                #[trigger] even_numbers[k] == arr[n] && 
                #[trigger] even_numbers[l] == arr[m]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut even_numbers = Vec::new();
    
    for i in 0..arr.len()
        invariant
            all_even_from_prefix(arr, i as int, even_numbers@),
            all_from_arr_prefix(arr, i as int, even_numbers@),
            order_preserved_prefix(arr, i as int, even_numbers@)
    {
        if is_even(arr[i]) {
            even_numbers.push(arr[i]);
        }
    }
    
    even_numbers
}
// </vc-code>

fn main() {
}

}