// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn concat_strings(strings: Seq<Seq<char>>, index: nat) -> Seq<char>
    decreases strings.len() - index
{
    if index >= strings.len() {
        Seq::<char>::empty()
    } else {
        strings[index as int] + concat_strings(strings, index + 1)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed requires/ensures from spec fn. */
spec fn sub_strings(strings: Seq<Seq<char>>, start: nat, end: nat) -> Seq<Seq<char>>
{
    if start == end {
        Seq::<Seq<char>>::empty()
    } else {
        Seq::<Seq<char>>::empty().push(strings[start as int]) + sub_strings(strings, start + 1, end)
    }
}
// </vc-helpers>

// <vc-spec>
fn concatenate(strings: Vec<Vec<char>>) -> (result: Vec<char>)
    ensures 
        result@ == concat_strings(strings@.map(|i, s: Vec<char>| s@), 0) &&
        (strings@.len() == 0 ==> result@ == Seq::<char>::empty())
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Added explicit proof for sub_strings in invariant to satisfy the compiler due to previous spec fn restrictions. */
{
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;

    while i < strings.len()
        invariant
            i <= strings.len(),
            result@ == concat_strings(sub_strings(strings@.map(|k, s: Vec<char>| s@), 0, i as nat), 0),
            0 <= i,
            i as nat <= strings@.len(),
            0 <= i as nat,
        decreases strings.len() - i
    {
        result.extend_from_slice(strings[i].as_slice());
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}