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
/* helper modified by LLM (iteration 5): Fixed type conversion in contains condition */
spec fn distinct_non_zero_count_spec(arr: Seq<int>) -> int {
    Set::<int>::new(|x: int| arr.contains(x) && x != 0).len() as int
}

spec fn vec_to_seq_int(arr: Vec<i8>) -> Seq<int> {
    arr@.map(|i, x| x as int)
}

proof fn distinct_non_zero_count_correctness(arr: Seq<int>) 
    ensures
        distinct_non_zero_count(arr) == distinct_non_zero_count_spec(arr)
{
    // Proof that both definitions are equivalent
    assert(distinct_non_zero_count(arr) == distinct_non_zero_count_spec(arr));
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
/* code modified by LLM (iteration 5): Fixed type conversion in invariant condition */
{
    let mut count: i8 = 0;
    let mut seen: Set<i8> = Set::empty();
    
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            count >= 0,
            count <= i as i8,
            seen.finite(),
            count as nat == seen.len(),
            forall|x: i8| seen.contains(x) ==> (x != 0 && arr@.contains(x as int))
        decreases arr.len() - i
    {
        let elem = arr[i];
        if elem != 0 && !seen.contains(elem) {
            seen = seen.insert(elem);
            count = count + 1;
        }
        i = i + 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}