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

/* code modified by LLM (iteration 3): added explicit type annotations for integer literals */
spec fn count_identical_from_start(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>) -> (result: int)
    decreases s1.len(),
{
    if s1.len() == 0 || s2.len() == 0 || s3.len() == 0 {
        0
    } else {
        (if s1[0] == s2[0] && s2[0] == s3[0] { 1int } else { 0int }) +
        count_identical_from_start(s1.skip(1), s2.skip(1), s3.skip(1))
    }
}

/* code modified by LLM (iteration 2): lemma to prove equivalence of counting methods */
proof fn count_identical_equivalence(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>)
    requires s1.len() == s2.len() == s3.len(),
    ensures count_identical(s1, s2, s3) == count_identical_from_start(s1, s2, s3),
    decreases s1.len(),
{
    if s1.len() == 0 {
        // base case
    } else {
        count_identical_equivalence(s1.drop_last(), s2.drop_last(), s3.drop_last());
        count_identical_equivalence(s1.skip(1), s2.skip(1), s3.skip(1));
        
        // The counts are the same, just computed in different orders
        assert(s1.drop_last()[0] == s1[0]);
        assert(s2.drop_last()[0] == s2[0]);
        assert(s3.drop_last()[0] == s3[0]);
    }
}

/* code modified by LLM (iteration 2): lemma relating take operation to counting from start */
proof fn count_take_lemma(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>, k: int)
    requires 
        s1.len() == s2.len() == s3.len(),
        0 <= k <= s1.len(),
    ensures count_identical_from_start(s1.take(k), s2.take(k), s3.take(k)) == count_identical_from_start(s1, s2, s3).min(k),
    decreases k,
{
    if k == 0 {
        // base case
    } else if k == 1 {
        // base case
    } else {
        count_take_lemma(s1.skip(1), s2.skip(1), s3.skip(1), k - 1);
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
    
    /* code modified by LLM (iteration 2): use equivalence lemma to establish relationship */
    proof {
        count_identical_equivalence(arr1@, arr2@, arr3@);
    }
    
    /* code modified by LLM (iteration 2): updated loop invariants to use counting equivalence */
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            arr1.len() == arr2.len() == arr3.len(),
            0 <= count <= i,
            count_identical_from_start(arr1@.take(i as int), arr2@.take(i as int), arr3@.take(i as int)) == count,
        decreases arr1.len() - i,
    {
        /* code modified by LLM (iteration 2): ensure bounds before array access */
        assert(i < arr1.len() && i < arr2.len() && i < arr3.len());
        
        if arr1[i] == arr2[i] && arr2[i] == arr3[i] {
            count = count + 1;
        }
        
        /* code modified by LLM (iteration 2): manual proof of invariant maintenance */
        proof {
            assert(arr1@.take((i + 1) as int) == arr1@.take(i as int).push(arr1[i as int]));
            assert(arr2@.take((i + 1) as int) == arr2@.take(i as int).push(arr2[i as int]));
            assert(arr3@.take((i + 1) as int) == arr3@.take(i as int).push(arr3[i as int]));
        }
        
        i = i + 1;
    }
    
    /* code modified by LLM (iteration 2): final proof that result equals original count_identical */
    proof {
        assert(i == arr1.len());
        assert(arr1@.take(i as int) =~= arr1@);
        assert(arr2@.take(i as int) =~= arr2@);
        assert(arr3@.take(i as int) =~= arr3@);
        assert(count_identical_from_start(arr1@, arr2@, arr3@) == count);
        // equivalence lemma already applied above
    }
    
    count
}

} // verus!

fn main() {}