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
    /* code modified by LLM (iteration 5): Added lemma to prove filter preservation */
    let mut even_list = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            even_list@ == arr@.take(i as int).filter(|x: u32| x % 2 == 0),
        decreases arr.len() - i,
    {
        let old_even_list = even_list;
        let old_i = i;
        
        if arr[i] % 2 == 0 {
            even_list.push(arr[i]);
            proof {
                assert(arr@.take((old_i + 1) as int) == arr@.take(old_i as int).push(arr@[old_i as int]));
                assert(arr@[old_i as int] % 2 == 0);
                assert(arr@.take((old_i + 1) as int).filter(|x: u32| x % 2 == 0) == 
                       arr@.take(old_i as int).filter(|x: u32| x % 2 == 0).push(arr@[old_i as int]));
                assert(even_list@ == old_even_list@.push(arr@[old_i as int]));
                assert(even_list@ == arr@.take((old_i + 1) as int).filter(|x: u32| x % 2 == 0));
            }
        } else {
            proof {
                assert(arr@.take((old_i + 1) as int) == arr@.take(old_i as int).push(arr@[old_i as int]));
                assert(arr@[old_i as int] % 2 != 0);
                assert(arr@.take((old_i + 1) as int).filter(|x: u32| x % 2 == 0) == 
                       arr@.take(old_i as int).filter(|x: u32| x % 2 == 0));
                assert(even_list@ == arr@.take((old_i + 1) as int).filter(|x: u32| x % 2 == 0));
            }
        }
        i = i + 1;
        assert(even_list@ == arr@.take(i as int).filter(|x: u32| x % 2 == 0));
    }
    assert(arr@.take(arr.len() as int) == arr@);
    even_list
}
// </vc-code>

}
fn main() {}