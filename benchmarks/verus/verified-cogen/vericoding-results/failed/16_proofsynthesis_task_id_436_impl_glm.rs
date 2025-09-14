// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn push_filter_lemma(seq: Seq<i32>, elem: i32)
    ensures 
        (seq + [elem]).filter(|x:i32| x < 0) == 
        seq.filter(|x:i32| x < 0) + (if elem < 0 then Seq::new(1, |i: int| 0 == i ==> elem) else Seq::empty())
{
    if elem < 0 {
        assert((seq + [elem]).filter(|x: i32| x < 0) == seq.filter(|x: i32| x < 0) + Seq::new(1, |i: int| 0 == i ==> elem));
    } else {
        assert((seq + [elem]).filter(|x: i32| x < 0) == seq.filter(|x: i32| x < 0));
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
    /* code modified by LLM (iteration 5): fixed syntax error in filter operation */
    let mut negative_list = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i as int <= arr@.len(),
            negative_list@ == arr@.subrange(0, i as int).filter(|x: i32| x < 0)
        decreases arr@.len() - i
    {
        let old_i = i;
        let elem = arr[i];
        push_filter_lemma(arr@.subrange(0, old_i as int), elem);
        if elem < 0 {
            negative_list.push(elem);
        }
        i += 1;
    }
    negative_list
}
// </vc-code>

}
fn main() {}