// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn all_even(a: Seq<int>) -> bool {
    forall|i: int| 0 <= i < a.len() ==> a[i] % 2 == 0
}

spec fn has_odd(a: Seq<int>) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i] % 2 == 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed to proof function to fix exec mode call error */
proof fn lemma_has_odd_at_index(a: Seq<int>, idx: int)
    requires
        0 <= idx < a.len(),
        a[idx] % 2 == 1,
    ensures
        has_odd(a),
{
}
// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>) -> (result: &'static str)
    ensures 
        (result == "Second") <==> all_even(a@.map(|i: int, x: i8| x as int)),
        (result == "First") <==> has_odd(a@.map(|i: int, x: i8| x as int)),
        result == "First" || result == "Second",
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed lemma call in proof block */
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a@[j] as int % 2 == 0,
        decreases a.len() - i
    {
        if a[i] % 2 == 1 {
            proof {
                lemma_has_odd_at_index(a@.map(|i: int, x: i8| x as int), i as int);
            }
            return "First";
        }
        i += 1;
    }
    "Second"
}
// </vc-code>


}

fn main() {}