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
/* code modified by LLM (iteration 5): use (a[j] as int) %2 ==1 and ==0 in invariant and set for consistent spec */
    let mut i: usize = 0;
    let mut found_odd: bool = false;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            found_odd == (exists |j: int| 0 <= j < i && (a@[j] as int) % 2 == 1),
            !found_odd ==> forall |j: int| 0 <= j < i ==> (a@[j] as int) % 2 == 0,
        decreases a.len() - i
    {
        if (a[i] as int) % 2 == 1 {
            found_odd = true;
        }
        i = i + 1;
    }
    proof {
        if !found_odd {
            assert(all_even(a@.map(|i: int, x: i8| x as int)));
        } else {
            assert(has_odd(a@.map(|i: int, x: i8| x as int)));
        }
    }
    if found_odd {
        "First"
    } else {
        "Second"
    }
}
// </vc-code>


}

fn main() {}