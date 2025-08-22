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

/* code modified by LLM (iteration 1): completely rewrote lemma to properly handle the relationship between spec function and subranges */
proof fn lemma_count_identical_extend(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>, i: int)
    requires
        s1.len() == s2.len() == s3.len(),
        0 <= i < s1.len(),
    ensures
        count_identical(s1.subrange(0, i + 1), s2.subrange(0, i + 1), s3.subrange(0, i + 1)) == 
        count_identical(s1.subrange(0, i), s2.subrange(0, i), s3.subrange(0, i)) + 
        (if s1[i] == s2[i] && s2[i] == s3[i] { 1int } else { 0int }),
    decreases i,
{
    let sub1 = s1.subrange(0, i + 1);
    let sub2 = s2.subrange(0, i + 1);
    let sub3 = s3.subrange(0, i + 1);
    
    // Key insight: the spec function works from the end, so we need to show
    // that the last element of our subrange corresponds to position i
    assert(sub1.last() == s1[i]);
    assert(sub2.last() == s2[i]);
    assert(sub3.last() == s3[i]);
    
    // Show that dropping the last element gives us the subrange up to i
    assert(sub1.drop_last() == s1.subrange(0, i));
    assert(sub2.drop_last() == s2.subrange(0, i));
    assert(sub3.drop_last() == s3.subrange(0, i));
    
    // The spec function definition directly gives us the result
    assert(count_identical(sub1, sub2, sub3) == 
           count_identical(sub1.drop_last(), sub2.drop_last(), sub3.drop_last()) + 
           (if sub1.last() == sub2.last() && sub2.last() == sub3.last() { 1int } else { 0int }));
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
    
    /* code modified by LLM (iteration 1): updated loop invariant and added proof steps to maintain invariant */
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            0 <= count <= i,
            arr1.len() == arr2.len() && arr2.len() == arr3.len(),
            count == count_identical(arr1@.subrange(0, i as int), arr2@.subrange(0, i as int), arr3@.subrange(0, i as int)),
        decreases arr1.len() - i,
    {
        /* code modified by LLM (iteration 1): added proof step before updating count */
        proof {
            lemma_count_identical_extend(arr1@, arr2@, arr3@, i as int);
        }
        
        if arr1[i] == arr2[i] && arr2[i] == arr3[i] {
            count = count + 1;
        }
        i = i + 1;
    }
    
    /* code modified by LLM (iteration 1): added assertion to help prove postcondition */
    assert(i == arr1.len());
    assert(arr1@.subrange(0, i as int) == arr1@);
    assert(arr2@.subrange(0, i as int) == arr2@);
    assert(arr3@.subrange(0, i as int) == arr3@);
    
    count
}

} // verus!

fn main() {}