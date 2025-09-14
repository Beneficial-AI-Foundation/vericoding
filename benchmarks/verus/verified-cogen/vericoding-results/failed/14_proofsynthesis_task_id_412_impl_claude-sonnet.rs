// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemma for filter properties on sequences */
proof fn filter_push_lemma<T>(s: Seq<T>, x: T, pred: spec_fn(T) -> bool)
    ensures
        s.push(x).filter(pred) == if pred(x) { s.filter(pred).push(x) } else { s.filter(pred) },
{ }
// </vc-helpers>

// <vc-spec>
fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)

    ensures
        even_list@ == arr@.filter(|x: u32| x % 2 == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use helper lemma to prove filter properties */
    let mut result = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0),
        decreases arr.len() - i
    {
        if arr[i] % 2 == 0 {
            result.push(arr[i]);
            proof {
                filter_push_lemma(arr@.subrange(0, i as int), arr@[i as int], |x: u32| x % 2 == 0);
            }
        } else {
            proof {
                filter_push_lemma(arr@.subrange(0, i as int), arr@[i as int], |x: u32| x % 2 == 0);
            }
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}