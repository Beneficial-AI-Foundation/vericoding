// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): spec for prefix all less-than using int indices */
spec fn all_lt(n: i32, a: &Vec<i32>, len: int) -> bool
{
    forall|j: int| 0 <= j < len ==> n > a[j]
}
// </vc-helpers>

// <vc-spec>
fn is_greater(n: i32, a: &Vec<i32>) -> (result: bool)
    requires a.len() > 0,
    ensures result == (forall|i: int| 0 <= i < a.len() ==> n > a[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): iterate and check all elements less-than n, using found_bad invariant */
    let mut i: usize = 0;
    let mut found_bad: bool = false;
    while i < a.len()
        invariant
            0 <= i as int && i as int <= a.len() as int,
            found_bad == (exists|j: int| 0 <= j < i as int && !(n > a[j])),
        decreases a.len() as int - i as int
    {
        if !(n > a[i]) {
            found_bad = true;
            i = a.len();
        } else {
            i = i + 1;
        }
    }
    let result: bool = !found_bad;
    proof {
        // show i == a.len()
        assert(!(i < a.len()));
        assert(i as int >= a.len() as int);
        assert(i as int <= a.len() as int);
        assert(i as int == a.len() as int);
        assert(found_bad == (exists|j: int| 0 <= j < a.len() as int && !(n > a[j])));
        if found_bad {
            assert(exists|j: int| 0 <= j < a.len() as int && !(n > a[j]));
            assert(!(forall|j: int| 0 <= j < a.len() as int ==> n > a[j]));
        } else {
            assert(!(exists|j: int| 0 <= j < a.len() as int && !(n > a[j])));
            assert(forall|j: int| 0 <= j < a.len() as int ==> n > a[j]);
        }
        assert(result == (forall|j: int| 0 <= j < a.len() as int ==> n > a[j]));
    }
    result
}
// </vc-code>

}
fn main() {}