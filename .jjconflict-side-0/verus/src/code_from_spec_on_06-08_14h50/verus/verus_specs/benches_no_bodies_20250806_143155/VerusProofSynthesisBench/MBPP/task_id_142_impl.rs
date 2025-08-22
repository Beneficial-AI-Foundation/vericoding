use vstd::prelude::*;

verus! {

spec fn count_identical(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>) -> (result: int)
    decreases s1.len(), s2.len(), s3.len(),
{
    if s1.len() == 0 || s2.len() == 0 || s3.len() == 0 {
        0
    } else {
        count_identical(s1.drop_last(), s2.drop_last(), s3.drop_last()) + if (s1.last() == s2.last()
            && s2.last() == s3.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}
// pure-end

fn count_identical_position(arr1: &Vec<i32>, arr2: &Vec<i32>, arr3: &Vec<i32>) -> (count: usize)
    // pre-conditions-start
    requires
        arr1.len() == arr2.len() && arr2.len() == arr3.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= count <= arr1.len(),
        count_identical(arr1@, arr2@, arr3@) == count,
    // post-conditions-end
{
    let mut count = 0;
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to fix compilation error */
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            arr1.len() == arr2.len() && arr2.len() == arr3.len(),
            count <= i,
            count == count_identical(arr1@.take(i as int), arr2@.take(i as int), arr3@.take(i as int)),
        decreases arr1.len() - i,
    {
        if arr1[i] == arr2[i] && arr2[i] == arr3[i] {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(arr1@.take(arr1.len() as int) == arr1@);
        assert(arr2@.take(arr2.len() as int) == arr2@);
        assert(arr3@.take(arr3.len() as int) == arr3@);
    }
    
    count
}

} // verus!

fn main() {}