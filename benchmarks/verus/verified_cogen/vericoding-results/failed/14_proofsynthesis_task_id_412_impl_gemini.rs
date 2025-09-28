// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)

    ensures
        even_list@ == arr@.filter(|x: u32| x % 2 == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed the compilation error by using the correct lemma `lemma_filter_distributes_push` from `vstd::seq`. */
    let mut even_list = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            even_list@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0),
        decreases arr.len() - i,
    {
        let elem = arr[i];

        proof {
            let f = |x: u32| x % 2 == 0;
            vstd::seq::lemma_filter_distributes_push(
                arr@.subrange(0, i as int),
                f,
                arr@[i as int]
            );
        }

        if elem % 2 == 0 {
            even_list.push(elem);
        }
        i = i + 1;
    }
    even_list
}
// </vc-code>

}
fn main() {}