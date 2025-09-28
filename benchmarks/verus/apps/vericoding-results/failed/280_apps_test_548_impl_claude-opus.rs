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
    /* code modified by LLM (iteration 5): Fixed type error in trigger - removed incorrect implication */
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] (a@.map(|k: int, x: i8| x as int))[j] % 2 == 0,
        decreases a.len() - i
    {
        if a[i] % 2 == 1 {
            assert(has_odd(a@.map(|k: int, x: i8| x as int))) by {
                assert((a@.map(|k: int, x: i8| x as int))[i as int] % 2 == 1);
            };
            return "First";
        }
        i = i + 1;
    }
    assert(all_even(a@.map(|k: int, x: i8| x as int))) by {
        assert(forall|j: int| 0 <= j < a.len() ==> (a@.map(|k: int, x: i8| x as int))[j] % 2 == 0);
    };
    "Second"
}
// </vc-code>


}

fn main() {}