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
/* helper modified by LLM (iteration 4): prefix_count helper with int parameter and bounds */
spec fn prefix_count(arr1: &Vec<i32>, arr2: &Vec<i32>, arr3: &Vec<i32>, n: int) -> int
    requires
        0 <= n, n <= arr1.len() as int,
    decreases n
{
    if n == 0 {
        0
    } else {
        prefix_count(arr1, arr2, arr3, n - 1) + if arr1@[(n - 1) as int] == arr2@[(n - 1) as int] && arr2@[(n - 1) as int] == arr3@[(n - 1) as int] { 1 as int } else { 0 as int }
    }
}

/* helper modified by LLM (iteration 4): proof that prefix_count equals count_identical for full length */
proof fn prefix_count_matches_count_identical(arr1: &Vec<i32>, arr2: &Vec<i32>, arr3: &Vec<i32>)
    requires
        arr1.len() == arr2.len() && arr2.len() == arr3.len(),
    ensures
        prefix_count(arr1, arr2, arr3, arr1.len() as int) == count_identical(arr1@, arr2@, arr3@),
{
    let len = arr1.len();
    if len == 0 {
        assert(prefix_count(arr1, arr2, arr3, 0) == 0);
        assert(count_identical(arr1@, arr2@, arr3@) == 0);
    } else {
        let arr1p = arr1[..len - 1].to_vec();
        let arr2p = arr2[..len - 1].to_vec();
        let arr3p = arr3[..len - 1].to_vec();
        prefix_count_matches_count_identical(&arr1p, &arr2p, &arr3p);
        assert(prefix_count(arr1, arr2, arr3, len as int) == prefix_count(&arr1p, &arr2p, &arr3p, (len - 1) as int) + if arr1@[(len - 1) as int] == arr2@[(len - 1) as int] && arr2@[(len - 1) as int] == arr3@[(len - 1) as int] { 1 as int } else { 0 as int });
        assert(count_identical(arr1@, arr2@, arr3@) == count_identical(arr1p@, arr2p@, arr3p@) + if arr1@[(len - 1) as int] == arr2@[(len - 1) as int] && arr2@[(len - 1) as int] == arr3@[(len - 1) as int] { 1 as int } else { 0 as int });
        assert(prefix_count(&arr1p, &arr2p, &arr3p, (len - 1) as int) == count_identical(arr1p@, arr2p@, arr3p@));
        assert(prefix_count(arr1, arr2, arr3, len as int) == count_identical(arr1@, arr2@, arr3@));
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
    /* code modified by LLM (iteration 4): iterate and maintain prefix_count invariant using int parameter */
    let mut i: usize = 0;
    let mut cnt: usize = 0;
    let n = arr1.len();
    while i < n
        invariant
            i <= n,
            cnt as int == prefix_count(arr1, arr2, arr3, i as int),
        decreases n - i
    {
        if arr1[i] == arr2[i] && arr2[i] == arr3[i] {
            cnt = cnt + 1;
        }
        i = i + 1;
    }
    proof {
        assert(cnt as int == prefix_count(arr1, arr2, arr3, n as int));
        prefix_count_matches_count_identical(arr1, arr2, arr3);
        assert(count_identical(arr1@, arr2@, arr3@) == prefix_count(arr1, arr2, arr3, n as int));
    }
    cnt
}

// </vc-code>

}
fn main() {}