// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn append_array_to_seq(s: Seq<i32>, a: &Vec<i32>) -> (r: Seq<i32>)
    ensures
        r.len() == s.len() + a.len(),
        forall|i: int| 0 <= i < s.len() ==> r[i] == s[i],
        forall|i: int| 0 <= i < a.len() ==> r[s.len() + i] == a[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Corrected the name of the sequence associativity lemma to fix a compilation error. */
    let mut result = s;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result === s.add(a.view().subrange(0, i as int)),
        decreases a.len() - i
    {
        proof {
            vstd::seq_lib::lemma_seq_add_associative(s, a.view().subrange(0, i as int), seq![a[i]]);
        }
        result = result.push(a[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}