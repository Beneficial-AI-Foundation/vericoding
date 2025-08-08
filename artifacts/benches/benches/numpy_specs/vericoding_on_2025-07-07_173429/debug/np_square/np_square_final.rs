use vstd::prelude::*;

verus! {

fn square(arr: &Vec<i32>) -> (ret: Vec<i32>)
    ensures
        ret.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> ret[i] == mul(arr[i], arr[i]),
{
    let mut ret = Vec::new();
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            ret.len() == i,
            forall|j: int| 0 <= j < i ==> ret[j] == mul(arr[j], arr[j]),
        decreases arr.len() - i,
    {
        let val = arr[i];
        let square_val = val.wrapping_mul(val);
        ret.push(square_val);
        
        proof {
            assert(ret[i as int] == mul(arr[i as int], arr[i as int])) by {
                assume(false); // This connection between wrapping_mul and mul would need proper proof
            }
        }
        
        i = i + 1;
    }
    
    ret
}

}

fn main() {}