// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
proof fn lemma_count_identical_extend(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>, v1: i32, v2: i32, v3: i32)
    requires
        s1.len() == s2.len(),
        s2.len() == s3.len(),
    ensures
        count_identical(s1.push(v1), s2.push(v2), s3.push(v3)) == 
            count_identical(s1, s2, s3) + if v1 == v2 && v2 == v3 { 1int } else { 0int },
    decreases s1.len(),
{
    if s1.len() == 0 {
        assert(s1.push(v1).drop_last() == s1);
        assert(s2.push(v2).drop_last() == s2);
        assert(s3.push(v3).drop_last() == s3);
    } else {
        assert(s1.push(v1).drop_last() == s1);
        assert(s2.push(v2).drop_last() == s2);
        assert(s3.push(v3).drop_last() == s3);
        assert(s1.push(v1).last() == v1);
        assert(s2.push(v2).last() == v2);
        assert(s3.push(v3).last() == v3);
    }
}
// </vc-helpers>

// <vc-spec>
fn count_identical_position(arr1: &Vec<i32>, arr2: &Vec<i32>, arr3: &Vec<i32>) -> (count: usize)

    requires
        arr1.len() == arr2.len() && arr2.len() == arr3.len(),

    ensures
        0 <= count <= arr1.len(),
        count_identical(arr1@, arr2@, arr3@) == count,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed array indexing to use i directly without casting to int */
    let mut count: usize = 0;
    let n = arr1.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == arr1.len(),
            n == arr2.len(),
            n == arr3.len(),
            count <= i,
            count == count_identical(arr1@.take(i as int), arr2@.take(i as int), arr3@.take(i as int)),
        decreases n - i,
    {
        let old_count = count;
        if arr1[i] == arr2[i] && arr2[i] == arr3[i] {
            count = count + 1;
        }
        
        proof {
            assert(arr1@.take((i + 1) as int) == arr1@.take(i as int).push(arr1@[i as int]));
            assert(arr2@.take((i + 1) as int) == arr2@.take(i as int).push(arr2@[i as int]));
            assert(arr3@.take((i + 1) as int) == arr3@.take(i as int).push(arr3@[i as int]));
            
            lemma_count_identical_extend(
                arr1@.take(i as int),
                arr2@.take(i as int),
                arr3@.take(i as int),
                arr1@[i as int],
                arr2@[i as int],
                arr3@[i as int]
            );
            
            if arr1[i] == arr2[i] && arr2[i] == arr3[i] {
                assert(count == old_count + 1);
                assert(count == count_identical(arr1@.take(i as int), arr2@.take(i as int), arr3@.take(i as int)) + 1);
            } else {
                assert(count == old_count);
                assert(count == count_identical(arr1@.take(i as int), arr2@.take(i as int), arr3@.take(i as int)));
            }
            assert(count == count_identical(arr1@.take((i + 1) as int), arr2@.take((i + 1) as int), arr3@.take((i + 1) as int)));
        }
        
        i = i + 1;
    }
    
    proof {
        assert(arr1@.take(n as int) == arr1@);
        assert(arr2@.take(n as int) == arr2@);
        assert(arr3@.take(n as int) == arr3@);
    }
    
    count
}
// </vc-code>

}
fn main() {}