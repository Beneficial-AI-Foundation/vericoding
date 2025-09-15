// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn contains_consecutive_numbers(a: &Vec<i32>) -> (result: bool)
    ensures
        result <==> exists|i: int| {
            &&& 0 <= i < a.len() - 1
            &&& #[trigger] a[i] + 1 == a[(i + 1) as int]
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Removed trailing commas from invariants to fix compilation error. */
    let len: int = a.len() as int;
    if len <= 1 {
        return false;
    }
    let mut i: int = 0;
    while i < len - 1
        invariant 0 <= i
        invariant i <= len - 1
        invariant forall|j: int| 0 <= j < i ==> !(#[trigger] (a@[j as int] as int + 1) == a@[(j + 1) as int] as int)
        decreases len - 1 - i
    {
        if #[trigger] ((a@[i as int] as int + 1) == a@[(i + 1) as int] as int) {
            proof {
                assert(a@[i as int] as int + 1 == a@[(i + 1) as int] as int);
            }
            return true;
        }
        i = i + 1;
    }
    proof {
        assert(!exists|j: int| 0 <= j < len - 1 && #[trigger] (a@[j as int] as int + 1 == a@[(j + 1) as int] as int));
    }
    return false;
}
// </vc-code>

}
fn main() {}