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

/* code modified by LLM (iteration 2): added helper spec function for forward counting */
spec fn count_identical_forward(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>, end: int) -> int
    requires 0 <= end <= s1.len() && s1.len() == s2.len() && s2.len() == s3.len()
    decreases end
{
    if end == 0 {
        0
    } else {
        count_identical_forward(s1, s2, s3, end - 1) + if (s1[end - 1] == s2[end - 1] && s2[end - 1] == s3[end - 1]) {
            1 as int
        } else {
            0 as int
        }
    }
}

/* code modified by LLM (iteration 2): added lemma to prove equivalence of forward and backward counting */
proof fn lemma_count_identical_equiv(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>)
    requires s1.len() == s2.len() && s2.len() == s3.len()
    ensures count_identical(s1, s2, s3) == count_identical_forward(s1, s2, s3, s1.len() as int)
    decreases s1.len()
{
    if s1.len() == 0 {
        // base case
    } else {
        lemma_count_identical_equiv(s1.drop_last(), s2.drop_last(), s3.drop_last());
        assert(s1.drop_last().len() == s2.drop_last().len() == s3.drop_last().len());
        assert(s1[s1.len() - 1] == s1.last());
        assert(s2[s2.len() - 1] == s2.last());
        assert(s3[s3.len() - 1] == s3.last());
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
    
    /* code modified by LLM (iteration 2): fixed loop invariant and added bounds check */
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            arr1.len() == arr2.len() && arr2.len() == arr3.len(),
            0 <= count <= i,
            count == count_identical_forward(arr1@, arr2@, arr3@, i as int),
        decreases arr1.len() - i,
    {
        /* code modified by LLM (iteration 2): added explicit bounds check before array access */
        if i < arr1.len() && i < arr2.len() && i < arr3.len() && arr1[i] == arr2[i] && arr2[i] == arr3[i] {
            count = count + 1;
        }
        i = i + 1;
    }
    
    /* code modified by LLM (iteration 2): added proof that relates forward counting to original spec */
    proof {
        lemma_count_identical_equiv(arr1@, arr2@, arr3@);
        assert(count == count_identical_forward(arr1@, arr2@, arr3@, arr1.len() as int));
        assert(count_identical_forward(arr1@, arr2@, arr3@, arr1.len() as int) == count_identical(arr1@, arr2@, arr3@));
    }
    
    count
}

} // verus!