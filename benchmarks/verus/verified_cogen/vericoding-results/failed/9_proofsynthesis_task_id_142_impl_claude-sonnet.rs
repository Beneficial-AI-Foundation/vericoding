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
/* helper modified by LLM (iteration 5): simplified lemma to focus on subrange-to-original relation */
proof fn count_identical_subrange_lemma(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>, n: int)
    requires
        0 <= n <= s1.len(),
        s1.len() == s2.len() && s2.len() == s3.len(),
    ensures
        count_identical(s1.subrange(0, n), s2.subrange(0, n), s3.subrange(0, n)) ==
        if n == 0 { 0 } else {
            count_identical(s1.subrange(0, n - 1), s2.subrange(0, n - 1), s3.subrange(0, n - 1)) +
            if s1[n - 1] == s2[n - 1] && s2[n - 1] == s3[n - 1] { 1int } else { 0int }
        },
        n == s1.len() ==> count_identical(s1.subrange(0, n), s2.subrange(0, n), s3.subrange(0, n)) == count_identical(s1, s2, s3),
    decreases n
{
    if n == 0 {
        // Base case: empty subrange
    } else {
        // Recursive case: prove the relationship
        count_identical_subrange_lemma(s1, s2, s3, n - 1);
        
        if n == s1.len() {
            // When n equals length, subrange equals full sequence
            assert(s1.subrange(0, n) == s1);
            assert(s2.subrange(0, n) == s2);
            assert(s3.subrange(0, n) == s3);
        }
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
    /* code modified by LLM (iteration 5): fixed loop and proof calls */
    let mut count = 0;
    let mut i = 0;
    
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            arr1.len() == arr2.len() && arr2.len() == arr3.len(),
            0 <= count <= i,
            count == count_identical(arr1@.subrange(0, i as int), arr2@.subrange(0, i as int), arr3@.subrange(0, i as int)),
        decreases arr1.len() - i
    {
        proof {
            count_identical_subrange_lemma(arr1@, arr2@, arr3@, (i + 1) as int);
        }
        
        if arr1[i] == arr2[i] && arr2[i] == arr3[i] {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        count_identical_subrange_lemma(arr1@, arr2@, arr3@, arr1.len() as int);
    }
    
    count
}
// </vc-code>

}
fn main() {}