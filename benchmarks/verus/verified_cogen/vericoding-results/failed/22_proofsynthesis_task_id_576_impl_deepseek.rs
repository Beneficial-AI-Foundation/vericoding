// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type mismatch between int and i32 in helper functions */
proof fn subarray_lemma(main: Seq<int>, sub: Seq<int>, k: int, l: int)
    requires
        0 <= k <= (main.len() - sub.len()) && l == k + sub.len(),
        main.subrange(k, l) =~= sub,
    ensures
        exists|k: int, l: int| 0 <= k <= (main.len() - sub.len()) && l == k + sub.len() && (#[trigger] (main.subrange(k, l))) =~= sub
{
}

spec fn find_subarray(main: Seq<int>, sub: Seq<int>, start: int) -> (found: bool)
    requires
        0 <= start <= main.len() - sub.len(),
    ensures
        found == (main.subrange(start, start + sub.len()) =~= sub)
{
    main.subrange(start, start + sub.len()) =~= sub
}
// </vc-helpers>

// <vc-spec>
fn is_sub_array(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)

    requires
        sub.len() <= main.len(),

    ensures
        result == (exists|k: int, l: int|
            0 <= k <= (main.len() - sub.len()) && l == k + sub.len() && (#[trigger] (main@.subrange(
                k,
                l,
            ))) =~= sub@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type conversion from Vec<i32> to Seq<int> */
{
    let mut i: usize = 0;
    let main_len: usize = main.len();
    let sub_len: usize = sub.len();
    
    while i <= main_len - sub_len
        invariant
            0 <= i <= main_len - sub_len + 1,
            forall|j: int| 0 <= j < i ==> !find_subarray(main@.map(|x| x as int), sub@.map(|x| x as int), j),
    {
        let mut j: usize = 0;
        let mut found_match = true;
        
        while j < sub_len
            invariant
                0 <= j <= sub_len,
                found_match == (forall|k: int| 0 <= k < j ==> (main@.map(|x| x as int)[i + k] == sub@.map(|x| x as int)[k])),
        {
            if main[i + j] != sub[j] {
                found_match = false;
                break;
            }
            j = j + 1;
        }
        
        if found_match {
            proof {
                subarray_lemma(main@.map(|x| x as int), sub@.map(|x| x as int), i as int, i as int + sub_len as int);
            }
            return true;
        }
        
        i = i + 1;
    }
    
    false
}
// </vc-code>

}
fn main() {}