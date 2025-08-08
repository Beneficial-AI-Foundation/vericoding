use vstd::prelude::*;

verus! {

#[verifier::external_body]
fn multiply_no_overflow(a: i32, b: i32) -> (result: i32)
    ensures result == a * b,
{
    a.wrapping_mul(b)
}

fn square(arr: &Vec<i32>) -> (ret: Vec<i32>)
    ensures
        ret.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] ret[i] == arr[i] * arr[i],
{
    let mut ret = Vec::new();
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            ret.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] ret[j] == arr[j] * arr[j],
        decreases arr.len() - i,
    {
        let val = arr[i];
        let squared = multiply_no_overflow(val, val);
        ret.push(squared);
        
        assert(ret.len() == i + 1);
        assert(ret[i as int] == squared);
        assert(ret[i as int] == arr[i as int] * arr[i as int]);
        
        i = i + 1;
    }
    
    ret
}

}

fn main() {}