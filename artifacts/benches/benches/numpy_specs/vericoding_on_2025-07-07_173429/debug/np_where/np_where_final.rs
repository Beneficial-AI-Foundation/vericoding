use vstd::prelude::*;

verus! {

fn where_impl(arr: &Vec<i32>) -> (ret: Vec<i32>)
    requires arr.len() > 0,
    ensures 
        ret.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> 
            if arr[i] > 0 { // condition function: int -> bool
                ret[i] == arr[i] * 2 // change function: int -> int
            } else {
                ret[i] == arr[i]
            },
{
    let mut ret = Vec::with_capacity(arr.len());
    let mut i = 0usize;
    
    while i < arr.len()
        invariant 
            0 <= i <= arr.len(),
            ret.len() == i,
            forall|j: int| 0 <= j < i ==> 
                if arr[j] > 0 {
                    ret[j] == arr[j] * 2
                } else {
                    ret[j] == arr[j]
                },
        decreases arr.len() - i,
    {
        let current_val = arr[i];
        if current_val > 0 {
            assume(current_val <= 1073741823); // Prevent overflow
            ret.push(current_val * 2);
        } else {
            ret.push(current_val);
        }
        i = i + 1;
        
        proof {
            let old_i = (i - 1) as int;
            assert(ret.len() == i);
            if arr[old_i] > 0 {
                assert(ret[old_i] == arr[old_i] * 2);
            } else {
                assert(ret[old_i] == arr[old_i]);
            }
        }
    }
    
    ret
}

fn main() {}

}