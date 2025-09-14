// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added comment for current iteration */
proof fn filter_subrange_lemma(s: Seq<i32>, i: int)
    requires 0 <= i < s.len()
    ensures s.subrange(0, i + 1).filter(|x: i32| x < 0) == if s[i] < 0 { s.subrange(0, i).filter(|x: i32| x < 0).push(s[i]) } else { s.subrange(0, i).filter(|x: i32| x < 0) }
{
}
// </vc-helpers>

// <vc-spec>
fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)

    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed unnecessary proof block that called a non-existent function */
    let mut negative_list = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            negative_list@ == arr@.subrange(0, i as int).filter(|x: i32| x < 0),
        decreases arr.len() - i,
    {
        let x = arr[i];
        if x < 0 {
            negative_list.push(x);
        }

        proof {
            filter_subrange_lemma(arr@, i as int);
        }

        i = i + 1;
    }

    negative_list
}
// </vc-code>

}
fn main() {}