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
/* helper modified by LLM (iteration 5): Fix seq mapping function signature and Vec indexing */
proof fn all_even_implies_not_has_odd(a: Seq<int>)
    requires
        all_even(a),
    ensures
        !has_odd(a),
{
    assert(forall|i: int| 0 <= i < a.len() ==> a[i] % 2 == 0);
    assert(!(exists|i: int| 0 <= i < a.len() && a[i] % 2 == 1));
}

proof fn has_odd_implies_not_all_even(a: Seq<int>)
    requires
        has_odd(a),
    ensures
        !all_even(a),
{
    assert(exists|i: int| 0 <= i < a.len() && a[i] % 2 == 1);
    assert(!forall|i: int| 0 <= i < a.len() ==> a[i] % 2 == 0);
}

fn find_odd_index(a: &Vec<i8>) -> (index: usize)
    requires
        has_odd(a@),
    ensures
        index < a.len(),
        a@[index as int] % 2 == 1,
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> a@[j] % 2 == 0,
        decreases a.len() - i,
    {
        let val = a[i] as i8;
        if val % 2 != 0 {
            return i;
        }
        i += 1;
    }
    assert(false); // Should not reach here due to precondition
    0
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
    /* code modified by LLM (iteration 5): Use proper sequence operations */
    if has_odd(a@) {
        "First"
    } else {
        "Second"
    }
}
// </vc-code>


}

fn main() {}