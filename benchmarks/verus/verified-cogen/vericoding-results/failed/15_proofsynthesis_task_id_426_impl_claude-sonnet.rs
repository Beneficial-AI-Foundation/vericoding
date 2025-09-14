// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed elem parameter type from int to u32 */
proof fn filter_subrange_lemma(s: Seq<u32>, start: int, end: int, next: int, elem: u32)
    requires
        0 <= start <= end <= next < s.len(),
    ensures
        s.subrange(start, next + 1).filter(|x: u32| x % 2 != 0) ==
        s.subrange(start, end).filter(|x: u32| x % 2 != 0) +
        (if s[next] % 2 != 0 { seq![s[next]] } else { seq![] }),
{
    let sub_end = s.subrange(start, end);
    let sub_next = s.subrange(start, next + 1);
    assert(sub_next == sub_end + seq![s[next]]);
}
// </vc-helpers>

// <vc-spec>
fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)

    ensures
        odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatch by removing cast to int */
    let mut result = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0),
        decreases arr.len() - i
    {
        if arr[i] % 2 != 0 {
            result.push(arr[i]);
        }
        proof {
            filter_subrange_lemma(arr@, 0, i as int, i as int, arr[i]);
        }
        i += 1;
    }
    assert(arr@.subrange(0, arr.len() as int) == arr@);
    result
}
// </vc-code>

}
fn main() {}