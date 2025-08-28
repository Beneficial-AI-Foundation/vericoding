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
spec fn count_identical_prefix(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>, len: int) -> int
    decreases len
{
    if len == 0 || len < 0 || len > s1.len() || len > s2.len() || len > s3.len() {
        0
    } else {
        count_identical_prefix(s1, s2, s3, len - 1) + 
        if s1[len - 1] == s2[len - 1] && s2[len - 1] == s3[len - 1] { 1int } else { 0int }
    }
}

proof fn count_identical_eq_prefix(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>)
    requires s1.len() == s2.len() && s2.len() == s3.len()
    ensures count_identical(s1, s2, s3) == count_identical_prefix(s1, s2, s3, s1.len() as int)
    decreases s1.len()
{
    if s1.len() == 0 {
        // Base case
    } else {
        count_identical_eq_prefix(s1.drop_last(), s2.drop_last(), s3.drop_last());
        assert(s1.drop_last().len() == s2.drop_last().len());
        assert(s2.drop_last().len() == s3.drop_last().len());
        
        // Establish the connection between the two recursive definitions
        assert(count_identical(s1.drop_last(), s2.drop_last(), s3.drop_last()) == 
               count_identical_prefix(s1.drop_last(), s2.drop_last(), s3.drop_last(), s1.drop_last().len() as int));
        assert(s1.drop_last().len() == s1.len() - 1);
        assert(count_identical_prefix(s1.drop_last(), s2.drop_last(), s3.drop_last(), s1.drop_last().len() as int) ==
               count_identical_prefix(s1, s2, s3, s1.len() as int - 1));
        
        // Connect the last elements
        assert(s1.last() == s1[s1.len() - 1]);
        assert(s2.last() == s2[s2.len() - 1]);
        assert(s3.last() == s3[s3.len() - 1]);
    }
}

proof fn count_identical_prefix_monotonic(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>, i: int, j: int)
    requires 
        0 <= i <= j,
        j <= s1.len() && j <= s2.len() && j <= s3.len()
    ensures count_identical_prefix(s1, s2, s3, i) <= count_identical_prefix(s1, s2, s3, j)
    decreases j - i
{
    if i == j {
        // Base case
    } else {
        count_identical_prefix_monotonic(s1, s2, s3, i, j - 1);
    }
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
    let mut count = 0;
    let mut i = 0;
    
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            arr1.len() == arr2.len() && arr2.len() == arr3.len(),
            0 <= count <= i,
            count == count_identical_prefix(arr1@, arr2@, arr3@, i as int),
        decreases arr1.len() - i
    {
        if arr1[i] == arr2[i] && arr2[i] == arr3[i] {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        count_identical_eq_prefix(arr1@, arr2@, arr3@);
    }
    
    count
}
// </vc-code>

} // verus!

fn main() {}