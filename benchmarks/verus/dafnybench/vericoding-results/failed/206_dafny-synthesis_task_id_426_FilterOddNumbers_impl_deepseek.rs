use vstd::prelude::*;

verus! {

/**
 * Filter odd numbers from an array of numbers
 **/

spec fn is_odd(n: int) -> bool {
    n % 2 != 0
}

// <vc-helpers>
spec fn seq_contains_odd(seq: Seq<int>, n: int) -> bool {
    exists|i: int| 0 <= i < seq.len() && seq[i] == n
}

proof fn filter_odd_contains_proof(arr: Seq<int>, odd_list: Seq<int>)
    requires
        forall|i: int| 0 <= i < arr.len() && is_odd(arr[i]) ==> seq_contains_odd(odd_list, arr[i]),
    ensures
        forall|i: int| 0 <= i < arr.len() && is_odd(arr[i]) ==> odd_list.contains(arr[i]),
{
    assert forall|i: int| 0 <= i < arr.len() && is_odd(arr[i]) implies odd_list.contains(arr[i]) by {
        assert(seq_contains_odd(odd_list, arr[i]));
        assert(odd_list.contains(arr[i]));
    };
}

proof fn original_contains_implies_seq_contains(arr: Seq<int>, val: int)
    requires
        arr.contains(val),
    ensures
        seq_contains_odd(arr, val),
{
    assert(seq_contains_odd(arr, val));
}
// </vc-helpers>

// <vc-spec>
fn filter_odd_numbers(arr: &[int]) -> (odd_list: Vec<int>)
    ensures 
        // All numbers in the output are odd and exist in the input 
        forall|i: int| 0 <= i < odd_list.len() ==> is_odd(odd_list[i]) && arr@.contains(odd_list[i]),
        // All odd numbers in the input are in the output
        forall|i: int| 0 <= i < arr.len() && is_odd(arr[i]) ==> odd_list@.contains(arr[i]),
// </vc-spec>
// <vc-code>
{
    let mut odd_list = Vec::new();
    let mut idx: usize = 0;
    
    while idx < arr.len()
        invariant
            0 <= idx <= arr.len(),
            forall|i: int| 0 <= i < odd_list.len() ==> is_odd(odd_list@[i]) && arr@.contains(odd_list@[i]),
            forall|i: int| 0 <= i < idx && is_odd(arr[i]) ==> seq_contains_odd(odd_list@, arr[i]),
        decreases arr.len() - idx,
    {
        let elem = arr[idx];
        proof {
            original_contains_implies_seq_contains(arr@, elem);
        }
        if (elem % 2 != 0) {
            odd_list.push(elem);
            proof {
                assert(odd_list@.contains(elem));
            }
        }
        idx += 1;
    }
    
    proof {
        filter_odd_contains_proof(arr@, odd_list@);
    }
    
    odd_list
}
// </vc-code>

fn main() {}

}