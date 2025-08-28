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

// <vc-helpers>
proof fn lemma_count_identical_base(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>)
    requires
        s1.len() == 0 || s2.len() == 0 || s3.len() == 0,
    ensures
        count_identical(s1, s2, s3) == 0,
{
}

proof fn lemma_count_identical_inductive(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>)
    requires
        s1.len() > 0,
        s2.len() > 0,
        s3.len() > 0,
    ensures
        count_identical(s1, s2, s3) == count_identical(s1.drop_last(), s2.drop_last(), s3.drop_last()) + if (s1.last() == s2.last() && s2.last() == s3.last()) { 1 as int } else { 0 as int },
{
}

proof fn lemma_count_identical_subrange(arr1: Seq<i32>, arr2: Seq<i32>, arr3: Seq<i32>, i: int)
    requires
        0 <= i <= arr1.len(),
        arr1.len() == arr2.len(),
        arr2.len() == arr3.len(),
    ensures
        count_identical(arr1.subrange(0, i), arr2.subrange(0, i), arr3.subrange(0, i)) <= i,
{
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    let len = arr1.len();

    while i < len
        invariant
            0 <= i <= len,
            i <= arr1.len(),
            i <= arr2.len(),
            i <= arr3.len(),
            0 <= count <= i,
            count_identical(arr1@.subrange(0, i as int), arr2@.subrange(0, i as int), arr3@.subrange(0, i as int)) == count as int,
        decreases len - i
    {
        if i < arr1.len() && i < arr2.len() && i < arr3.len() && arr1[i] == arr2[i] && arr2[i] == arr3[i] {
            count = count + 1;
        }
        i = i + 1;
    }

    count
}
// </vc-code>

} // verus!

fn main() {}