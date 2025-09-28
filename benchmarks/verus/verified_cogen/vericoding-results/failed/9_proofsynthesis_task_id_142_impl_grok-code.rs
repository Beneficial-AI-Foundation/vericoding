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
/* helper modified by LLM (iteration 5): no changes needed, section remains empty */
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
/* code modified by LLM (iteration 5): fixed compilation error by accessing Vec elements directly instead of using sequence access in exec code */
    let mut count = 0usize;
    let mut i = 0usize;
    proof {
        assert(arr1.len() as int == arr2.len() as int);
        assert(arr2.len() as int == arr3.len() as int);
        assert(count_identical(arr1@, arr2@, arr3@) == count_identical(arr1@.take(i as int), arr2@.take(i as int), arr3@.take(i as int)));
    }
    while i < arr1.len()
        invariant
            0 <= i as int <= arr1.len() as int,
            arr1.len() as int == arr2.len() as int && arr2.len() as int == arr3.len() as int,
            0 <= count as int <= i as int,
            count_identical(arr1@.take(i as int), arr2@.take(i as int), arr3@.take(i as int)) == count as int,
        decreases arr1.len() - i,
    {
        if arr1[i] == arr2[i] && arr2[i] == arr3[i] {
            count += 1;
            proof {
                assert(arr1@.take(i as int + 1).last() == arr2@.take(i as int + 1).last() && arr2@.take(i as int + 1).last() == arr3@.take(i as int + 1).last());
                assert(count_identical(arr1@.take((i as int + 1)), arr2@.take((i as int + 1)), arr3@.take((i as int + 1))) == count_identical(arr1@.take(i as int), arr2@.take(i as int), arr3@.take(i as int)) + 1 as int);
            }
        }
        i += 1;
    }
    count
}
// </vc-code>

}
fn main() {}