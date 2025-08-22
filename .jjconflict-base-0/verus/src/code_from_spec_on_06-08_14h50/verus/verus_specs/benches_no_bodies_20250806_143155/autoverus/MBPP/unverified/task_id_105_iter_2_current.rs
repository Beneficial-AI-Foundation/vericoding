use vstd::prelude::*;

fn main() {}

verus! {

spec fn count_boolean(seq: Seq<bool>) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_boolean(seq.drop_last()) + if (seq.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}

fn count_true(arr: &Vec<bool>) -> (count: u64)
    ensures
        0 <= count <= arr.len(),
        count_boolean(arr@) == count,
{
    let mut count: u64 = 0;
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to fix verification error */
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            0 <= count <= i,
            count_boolean(arr@.take(i as int)) == count,
        decreases arr.len() - i,
    {
        if arr[i] {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(arr@.take(arr.len() as int) == arr@);
    }
    
    count
}

} // verus!