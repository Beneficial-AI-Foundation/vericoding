use vstd::prelude::*;

fn main() {}

verus! {

spec fn count_identical(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>) -> int
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

fn count_identical_position(arr1: &Vec<i32>, arr2: &Vec<i32>, arr3: &Vec<i32>) -> (count: usize)
    requires
        arr1.len() == arr2.len() && arr2.len() == arr3.len(),
    ensures
        0 <= count <= arr1.len(),
        count_identical(arr1@, arr2@, arr3@) == count,
{
    let mut count = 0;
    let mut i = 0;
    
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            0 <= count <= i,
            count_identical(arr1@.subrange(0, i as int), arr2@.subrange(0, i as int), arr3@.subrange(0, i as int)) == count,
    {
        if arr1[i] == arr2[i] && arr2[i] == arr3[i] {
            count = count + 1;
        }
        i = i + 1;
    }
    
    assert(arr1@.subrange(0, arr1.len() as int) =~= arr1@);
    assert(arr2@.subrange(0, arr2.len() as int) =~= arr2@);
    assert(arr3@.subrange(0, arr3.len() as int) =~= arr3@);
    
    count
}

} // verus!