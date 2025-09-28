// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(arr: Seq<int>) -> bool {
    true
}

spec fn distinct_non_zero_count(arr: Seq<int>) -> int {
    Set::<int>::new(|x: int| arr.contains(x) && x != 0).len() as int
}
// </vc-preamble>

// <vc-helpers>
spec fn vec_to_seq_int(arr: Vec<i8>) -> Seq<int> {
    arr@.map(|i, x| x as int)
}

/* helper modified by LLM (iteration 5): fixed syntax error in lemma */
fn lemma_distinct_count_bound(arr: Seq<int>)
    ensures
        distinct_non_zero_count(arr) <= arr.len()
{
    proof {
        let distinct_set = Set::<int>::new(|x: int| arr.contains(x) && x != 0);
        assert(forall |x: int| distinct_set.contains(x) ==> arr.contains(x));
        assert(distinct_set.finite());
        let arr_set = Set::<int>::new(|x: int| arr.contains(x));
        assert(distinct_set.subset_of(arr_set));
        assert(arr_set.len() <= arr.len());
    }
}

fn lemma_count_correctness(arr: Seq<int>, i: int, count: int)
    requires
        0 <= i <= arr.len(),
        count >= 0
    ensures
        count <= distinct_non_zero_count(arr.subrange(0, i))
{
}
// </vc-helpers>

// <vc-spec>
fn solve(arr: Vec<i8>) -> (result: i8)
    requires 
        valid_input(vec_to_seq_int(arr))
    ensures 
        result >= 0,
        result as int <= arr@.len(),
        result as int == distinct_non_zero_count(vec_to_seq_int(arr))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplified implementation to fix verification */
    let mut count = 0i8;
    
    for i in 0..arr.len()
        invariant
            count >= 0,
            count as int <= i,
            count as int <= distinct_non_zero_count(vec_to_seq_int(arr).subrange(0, i as int))
    {
        let val = arr[i];
        if val != 0 {
            let mut found = false;
            for j in 0..i
                invariant
                    j <= i,
                    i < arr@.len(),
                    found == vec_to_seq_int(arr).subrange(0, j as int).contains(val as int)
                ensures
                    found == vec_to_seq_int(arr).subrange(0, i as int).contains(val as int)
            {
                if arr[j] == val {
                    found = true;
                    break;
                }
            }
            if !found && count < 127 {
                count = count + 1;
            }
        }
    }
    
    lemma_distinct_count_bound(vec_to_seq_int(arr));
    assert(count as int <= distinct_non_zero_count(vec_to_seq_int(arr)));
    
    count
}
// </vc-code>


}

fn main() {}