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
proof fn count_identical_property(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>, n: nat)
    requires
        s1.len() == s2.len() && s2.len() == s3.len(),
        n <= s1.len(),
    ensures
        count_identical(s1.subrange(0, n as int), s2.subrange(0, n as int), s3.subrange(0, n as int)) >= 0,
        count_identical(s1.subrange(0, n as int), s2.subrange(0, n as int), s3.subrange(0, n as int)) <= n,
    decreases n,
{
    if n == 0 {
        assert(s1.subrange(0, 0).len() == 0);
    } else {
        count_identical_property(s1, s2, s3, (n - 1) as nat);
        assert(s1.subrange(0, n as int) =~= s1.subrange(0, (n - 1) as int).push(s1[(n - 1) as int]));
        assert(s1.subrange(0, n as int).drop_last() =~= s1.subrange(0, (n - 1) as int));
        assert(s2.subrange(0, n as int).drop_last() =~= s2.subrange(0, (n - 1) as int));
        assert(s3.subrange(0, n as int).drop_last() =~= s3.subrange(0, (n - 1) as int));
    }
}

proof fn count_identical_full_seq(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>)
    requires
        s1.len() == s2.len() && s2.len() == s3.len(),
    ensures
        count_identical(s1, s2, s3) >= 0,
        count_identical(s1, s2, s3) <= s1.len(),
    decreases s1.len(),
{
    if s1.len() == 0 {
    } else {
        count_identical_full_seq(s1.drop_last(), s2.drop_last(), s3.drop_last());
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
    proof {
        count_identical_full_seq(arr1@, arr2@, arr3@);
    }
    
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < arr1.len()
        invariant
            arr1.len() == arr2.len() && arr2.len() == arr3.len(),
            i <= arr1.len(),
            count <= i,
            count == count_identical(arr1@.subrange(0, i as int), arr2@.subrange(0, i as int), arr3@.subrange(0, i as int)),
        decreases arr1.len() - i,
    {
        if arr1[i] == arr2[i] && arr2[i] == arr3[i] {
            count = count + 1;
        }
        
        proof {
            let old_i = i;
            assert(arr1@.subrange(0, (i + 1) as int) =~= arr1@.subrange(0, i as int).push(arr1@[i as int]));
            assert(arr1@.subrange(0, (i + 1) as int).drop_last() =~= arr1@.subrange(0, i as int));
            assert(arr2@.subrange(0, (i + 1) as int).drop_last() =~= arr2@.subrange(0, i as int));
            assert(arr3@.subrange(0, (i + 1) as int).drop_last() =~= arr3@.subrange(0, i as int));
            assert(arr1@.subrange(0, (i + 1) as int).last() == arr1@[i as int]);
            assert(arr2@.subrange(0, (i + 1) as int).last() == arr2@[i as int]);
            assert(arr3@.subrange(0, (i + 1) as int).last() == arr3@[i as int]);
        }
        
        i = i + 1;
    }
    
    proof {
        assert(arr1@.subrange(0, arr1.len() as int) =~= arr1@);
        assert(arr2@.subrange(0, arr2.len() as int) =~= arr2@);
        assert(arr3@.subrange(0, arr3.len() as int) =~= arr3@);
    }
    
    count
}
// </vc-code>

} // verus!

fn main() {}