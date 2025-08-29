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
spec fn count_identical_prefix(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>, n: nat) -> int
    decreases n,
{
    if n == 0 {
        0
    } else {
        count_identical_prefix(s1, s2, s3, (n - 1) as nat) + if (s1[n - 1] == s2[n - 1] && s2[n - 1] == s3[n - 1]) {
            1int
        } else {
            0int
        }
    }
}

proof fn count_identical_equiv(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>)
    requires s1.len() == s2.len() && s2.len() == s3.len(),
    ensures count_identical(s1, s2, s3) == count_identical_prefix(s1, s2, s3, s1.len() as nat),
    decreases s1.len(),
{
    if s1.len() == 0 {
        /* code modified by LLM (iteration 5): base case is trivial */
    } else {
        /* code modified by LLM (iteration 5): recursive case with proper indexing */
        count_identical_equiv(s1.drop_last(), s2.drop_last(), s3.drop_last());
        assert(s1[s1.len() - 1] == s1.last());
        assert(s2[s2.len() - 1] == s2.last());
        assert(s3[s3.len() - 1] == s3.last());
    }
}

proof fn count_identical_prefix_bound(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>, n: nat)
    requires s1.len() == s2.len() && s2.len() == s3.len() && n <= s1.len(),
    ensures 0 <= count_identical_prefix(s1, s2, s3, n) <= n,
    decreases n,
{
    if n == 0 {
        /* code modified by LLM (iteration 5): base case */
    } else {
        /* code modified by LLM (iteration 5): recursive case */
        count_identical_prefix_bound(s1, s2, s3, (n - 1) as nat);
    }
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

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
    /* code modified by LLM (iteration 5): establish bounds proof at start */
    proof {
        count_identical_prefix_bound(arr1@, arr2@, arr3@, 0nat);
    }
    
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            arr1.len() == arr2.len() && arr2.len() == arr3.len(),
            count == count_identical_prefix(arr1@, arr2@, arr3@, i as nat),
            0 <= count <= i,
        decreases arr1.len() - i,
    {
        /* code modified by LLM (iteration 5): establish bounds before increment */
        proof {
            count_identical_prefix_bound(arr1@, arr2@, arr3@, (i + 1) as nat);
        }
        
        if arr1[i] == arr2[i] && arr2[i] == arr3[i] {
            count = count + 1;
        }
        i = i + 1;
    }
    
    /* code modified by LLM (iteration 5): prove equivalence and final bounds */
    proof {
        count_identical_equiv(arr1@, arr2@, arr3@);
        count_identical_prefix_bound(arr1@, arr2@, arr3@, arr1.len() as nat);
    }
    
    count
}
// </vc-code>

} // verus!

fn main() {}