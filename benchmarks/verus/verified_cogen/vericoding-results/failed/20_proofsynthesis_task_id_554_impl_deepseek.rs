// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Complete filter_lemma with proper sequence equality */
proof fn filter_lemma(arr: Seq<u32>, i: int, elem: u32)
    requires
        0 <= i && i < arr.len(),
        arr[i] == elem
    ensures
        is_odd_spec(elem) ==> arr.subrange(0, i + 1).filter(|x: u32| is_odd_spec(x)) == arr.subrange(0, i).filter(|x: u32| is_odd_spec(x)).push(elem),
        !is_odd_spec(elem) ==> arr.subrange(0, i + 1).filter(|x: u32| is_odd_spec(x)) == arr.subrange(0, i).filter(|x: u32| is_odd_spec(x))
{
    let filtered_prefix = arr.subrange(0, i).filter(|x: u32| is_odd_spec(x));
    let filtered_with_elem = arr.subrange(0, i + 1).filter(|x: u32| is_odd_spec(x));
    
    if is_odd_spec(elem) {
        assert(filtered_with_elem =~= filtered_prefix.push(elem)) by {
            assert(filtered_prefix.push(elem) =~= filtered_with_elem);
        }
        assert(filtered_with_elem == filtered_prefix.push(elem));
    } else {
        assert(filtered_prefix =~= filtered_with_elem) by {
            assert(filtered_with_elem =~= filtered_prefix);
        }
        assert(filtered_with_elem == filtered_prefix);
    }
}

spec fn is_odd_spec(x: u32) -> bool {
    x % 2 != 0
}
// </vc-helpers>

// <vc-spec>
fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)

    ensures
        odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed loop with proper proof structure and sequence equality */
{
    let mut odd_numbers = Vec::new();
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant 
            0 <= i && i <= arr@.len(),
            odd_numbers@ == arr@.subrange(0, i as int).filter(|x: u32| is_odd_spec(x)),
            forall|j: int| 0 <= j && j < odd_numbers@.len() ==> is_odd_spec(odd_numbers@[j])
        decreases arr.len() - i
    {
        let elem = arr[i];
        proof {
            filter_lemma(arr@, i as int, elem);
        }
        if elem % 2 != 0 {
            odd_numbers.push(elem);
        }
        i += 1;
    }
    
    odd_numbers
}
// </vc-code>

}
fn main() {}