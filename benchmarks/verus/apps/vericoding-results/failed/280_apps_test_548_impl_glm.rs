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
    /* code modified by LLM (iteration 5): removed cast to int to fix compilation error */
    for i in 0..a.len() {
        if a[i] % 2 != 0 {
            return "First";
        }
    }
    return "Second";
}
// </vc-code>


}

fn main() {}