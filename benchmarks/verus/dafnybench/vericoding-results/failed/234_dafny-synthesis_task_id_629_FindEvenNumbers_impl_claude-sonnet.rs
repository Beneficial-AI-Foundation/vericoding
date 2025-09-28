use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

// <vc-helpers>
proof fn lemma_even_preserved(x: i32)
    requires is_even(x as int)
    ensures is_even(x as int)
{
}

proof fn lemma_exists_in_slice(arr: &[i32], val: i32, idx: usize)
    requires 0 <= idx < arr.len()
    requires arr@[idx as int] == val
    ensures exists|j: int| 0 <= j < arr.len() && arr@[j] == val
{
}

proof fn lemma_exists_in_vec(v: &Vec<i32>, val: i32, idx: usize)
    requires 0 <= idx < v.len()
    requires v@[idx as int] == val
    ensures exists|j: int| 0 <= j < v.len() && v@[j] == val
{
}
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
    let mut even_list = Vec::new();
    
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|k: int| 0 <= k < even_list.len() ==> is_even(even_list@[k] as int) && exists|j: int| 0 <= j < arr.len() && arr@[j] == even_list@[k],
            forall|k: int| 0 <= k < i && is_even(arr@[k] as int) ==> exists|j: int| 0 <= j < even_list.len() && even_list@[j] == arr@[k]
    {
        if is_even(arr@[i as int] as int) {
            proof {
                lemma_even_preserved(arr@[i as int]);
                lemma_exists_in_slice(arr, arr@[i as int], i);
            }
            even_list.push(arr@[i as int]);
            proof {
                let new_idx = even_list.len() - 1;
                lemma_exists_in_vec(&even_list, arr@[i as int], new_idx);
            }
        }
        i += 1;
    }
    
    even_list
}
// </vc-code>

fn main() {
}

}