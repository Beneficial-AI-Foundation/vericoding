// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma by properly establishing the relationship using push property */
proof fn lemma_filter_extend(arr: Seq<i32>, i: int, x: i32)
    requires
        0 <= i < arr.len(),
        arr[i] == x,
    ensures
        arr.subrange(0, i + 1).filter(|y: i32| y < 0) == arr.subrange(0, i).filter(|y: i32| y < 0) + (if x < 0 { seq![x] } else { seq![] }),
{
    proof {
        let left_seq = arr.subrange(0, i);
        let extended_seq = arr.subrange(0, i + 1);
        
        assert(extended_seq == left_seq.push(x));
        
        let left_filtered = left_seq.filter(|y: i32| y < 0);
        let extended_filtered = extended_seq.filter(|y: i32| y < 0);
        
        if x < 0 {
            assert(extended_filtered == left_filtered + seq![x]);
        } else {
            assert(extended_filtered == left_filtered + seq![]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)

    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): moved proof before increment to match the invariant index */
    let mut negative_list: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            negative_list@ == arr@.subrange(0, i as int).filter(|x: i32| x < 0),
        decreases arr.len() - i
    {
        proof {
            lemma_filter_extend(arr@, i as int, arr@[i as int]);
        }
        if arr[i] < 0 {
            negative_list.push(arr[i]);
        }
        i += 1;
    }
    negative_list
}
// </vc-code>

}
fn main() {}