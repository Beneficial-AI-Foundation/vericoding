use vstd::prelude::*;

verus! {

spec fn check_find_first_odd(arr: &Vec<u32>, index: Option<usize>) -> (result: bool)
{
    if let Some(idx) = index {
        &&& arr@.take(idx as int) == arr@.take(idx as int).filter(|x: u32| x % 2 == 0)
        &&& arr[idx as int] % 2 != 0
    } else {
        forall|k: int| 0 <= k < arr.len() ==> (arr[k] % 2 == 0)
    }
}

//IMPL find_first_odd
fn find_first_odd(arr: &Vec<u32>) -> (index: Option<usize>)
    ensures check_find_first_odd(arr, index),
{
    for i in 0..arr.len()
        invariant forall|k: int| 0 <= k < i ==> (arr[k] % 2 == 0)
    {
        if arr[i] % 2 != 0 {
            /* code modified by LLM (iteration 1): Added proper proof that filtering even numbers from a sequence of all even numbers results in the same sequence */
            assert(arr@.take(i as int) == arr@.take(i as int).filter(|x: u32| x % 2 == 0)) by {
                let prefix = arr@.take(i as int);
                let filtered = prefix.filter(|x: u32| x % 2 == 0);
                
                // Prove that every element in the prefix is even
                assert(forall|j: int| 0 <= j < prefix.len() ==> prefix[j] % 2 == 0) by {
                    assert(forall|k: int| 0 <= k < i ==> arr[k] % 2 == 0);
                    assert(prefix.len() == i);
                    assert(forall|j: int| 0 <= j < prefix.len() ==> prefix[j] == arr[j]);
                }
                
                // Prove that the filtered sequence has the same length
                assert(filtered.len() == prefix.len()) by {
                    assert(forall|j: int| 0 <= j < prefix.len() ==> prefix[j] % 2 == 0);
                }
                
                // Prove elementwise equality
                assert(forall|j: int| 0 <= j < prefix.len() ==> prefix[j] == filtered[j]) by {
                    assert(forall|j: int| 0 <= j < prefix.len() ==> prefix[j] % 2 == 0);
                }
                
                // Conclude sequence equality
                assert(prefix =~= filtered);
            };
            
            /* code modified by LLM (iteration 1): Added assertion to prove that the element at index i is odd */
            assert(arr[i as int] % 2 != 0);
            return Some(i);
        }
    }
    None
}

} // verus!

fn main() {}