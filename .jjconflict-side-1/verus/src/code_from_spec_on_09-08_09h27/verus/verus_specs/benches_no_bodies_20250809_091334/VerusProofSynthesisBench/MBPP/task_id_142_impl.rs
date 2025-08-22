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

/* code modified by LLM (iteration 1): Added helper lemma to prove equivalence between recursive spec and iterative implementation */
proof fn lemma_count_identical_prefix(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>, i: int)
    requires
        s1.len() == s2.len() && s2.len() == s3.len(),
        0 <= i < s1.len(),
    ensures
        count_identical(s1.subrange(0, i + 1), s2.subrange(0, i + 1), s3.subrange(0, i + 1)) ==
        count_identical(s1.subrange(0, i), s2.subrange(0, i), s3.subrange(0, i)) +
        /* code modified by LLM (iteration 1): Fixed integer literal type annotation */ 
        if s1[i] == s2[i] && s2[i] == s3[i] { 1int } else { 0int },
    decreases s1.len() - i,
{
    let prefix_i = s1.subrange(0, i);
    let prefix_i1 = s1.subrange(0, i + 1);
    
    assert(prefix_i1.len() == i + 1);
    assert(prefix_i1.last() == s1[i]);
    assert(prefix_i1.drop_last() =~= prefix_i);
    
    let s2_prefix_i = s2.subrange(0, i);
    let s2_prefix_i1 = s2.subrange(0, i + 1);
    assert(s2_prefix_i1.last() == s2[i]);
    assert(s2_prefix_i1.drop_last() =~= s2_prefix_i);
    
    let s3_prefix_i = s3.subrange(0, i);
    let s3_prefix_i1 = s3.subrange(0, i + 1);
    assert(s3_prefix_i1.last() == s3[i]);
    assert(s3_prefix_i1.drop_last() =~= s3_prefix_i);
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
            arr1.len() == arr2.len() && arr2.len() == arr3.len(),
            0 <= i <= arr1.len(),
            0 <= count <= i,
            count == count_identical(arr1@.subrange(0, i as int), arr2@.subrange(0, i as int), arr3@.subrange(0, i as int)),
        /* code modified by LLM (iteration 2): Added decreases clause to prove loop termination */
        decreases arr1.len() - i
    {
        /* code modified by LLM (iteration 1): Added proof block to establish loop invariant maintenance */
        proof {
            lemma_count_identical_prefix(arr1@, arr2@, arr3@, i as int);
        }
        
        if arr1[i] == arr2[i] && arr2[i] == arr3[i] {
            count += 1;
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 1): Fixed nat to int type conversion in subrange calls */
    proof {
        assert(arr1@.subrange(0, arr1@.len() as int) =~= arr1@);
        assert(arr2@.subrange(0, arr2@.len() as int) =~= arr2@);
        assert(arr3@.subrange(0, arr3@.len() as int) =~= arr3@);
    }
    
    count
}

} // verus!

fn main() {}