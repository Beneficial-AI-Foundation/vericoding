use vstd::prelude::*;

verus! {

/**
 * Find negative numbers from an array of numbers
 **/

spec fn is_negative(n: int) -> bool {
    n < 0
}

// <vc-helpers>
spec fn seq_contains<T>(s: Seq<T>, elem: T) -> bool 
    where T: Eq
{
    exists|i: int| 0 <= i < s.len() && s[i] == elem
}

proof fn prove_contains_implies_exists_in_slice<T: Eq>(s: Seq<T>, slice: &[T], elem: T)
    requires
        s =~= slice@,
        seq_contains(s, elem),
    ensures
        exists|j: int| 0 <= j < slice.len() && slice[j] == elem,
{
}

proof fn prove_exists_in_slice_implies_contains<T: Eq>(s: Seq<T>, slice: &[T], elem: T)
    requires
        s =~= slice@,
        exists|j: int| 0 <= j < slice.len() && slice[j] == elem,
    ensures
        seq_contains(s, elem),
{
}
// </vc-helpers>

// <vc-spec>
fn find_negative_numbers(arr: &[int]) -> (negative_list: Vec<int>)
    ensures
        // All numbers in the output are negative and exist in the input
        forall|i: int| 0 <= i < negative_list.len() ==> 
            is_negative(negative_list[i]) && exists|j: int| 0 <= j < arr.len() && arr[j] == negative_list[i],
        // All negative numbers in the input are in the output
        forall|i: int| 0 <= i < arr.len() && is_negative(arr[i]) ==> 
            exists|j: int| 0 <= j < negative_list.len() && negative_list[j] == arr[i],
// </vc-spec>
// <vc-code>
{
    let mut negative_list = Vec::new();
    let mut idx: usize = 0;
    
    while idx < arr.len()
        invariant
            0 <= idx <= arr.len(),
            forall|i: int| 0 <= i < negative_list@.len() ==> 
                is_negative(negative_list@[i]) && exists|j: int| 0 <= j < arr.len() && arr[j] == negative_list@[i],
            forall|j: int| 0 <= j < idx && is_negative(arr[j]) ==> 
                exists|k: int| 0 <= k < negative_list@.len() && negative_list@[k] == arr[j],
    {
        let current_val = arr[idx];
        if current_val < 0 {
            negative_list.push(current_val);
            proof {
                let len = negative_list@.len() as int;
                assert(negative_list@[len - 1] == current_val);
                assert(exists|k: int| 0 <= k < len && negative_list@[k] == current_val) by {
                    assert(negative_list@[len - 1] == current_val);
                }
            }
        }
        
        proof {
            if current_val < 0 {
                assert(forall|j: int| 0 <= j < idx + 1 && is_negative(arr[j]) ==> 
                    exists|k: int| 0 <= k < negative_list@.len() && negative_list@[k] == arr[j]);
            } else {
                assert(forall|j: int| 0 <= j < idx + 1 && is_negative(arr[j]) ==> 
                    exists|k: int| 0 <= k < negative_list@.len() && negative_list@[k] == arr[j]);
            }
        }
        
        idx = idx + 1;
    }
    
    negative_list
}
// </vc-code>

fn main() {}

}