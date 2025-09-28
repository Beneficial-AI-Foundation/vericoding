// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn odd(n: nat) -> bool { n % 2 == 1 }
spec fn even(n: nat) -> bool { n % 2 == 0 }
// </vc-preamble>

// <vc-helpers>
spec fn all_odd(s: Seq<nat>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> odd(s[i])
}

spec fn all_even(s: Seq<nat>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> even(s[i])
}
// </vc-helpers>

// <vc-spec>
fn partitionOddEven(a: &mut Vec<nat>)
    ensures 
        a@.to_multiset() == old(a)@.to_multiset(),
        !(exists|i: int, j: int| 0 <= i < j < a@.len() && even(a@[i]) && odd(a@[j])),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed compilation error by manually swapping elements */
{
    let mut i: usize = 0;
    let len = a.len();
    let mut j: usize = len;
    while i < j
        invariant
            0 <= i <= j <= len,
            a@.len() == old(a)@.len(),
            a@.to_multiset() == old(a)@.to_multiset(),
            all_odd(a@.subrange(0, i as int)),
            all_even(a@.subrange(j as int, len as int)),
        decreases (j - i) as int
    {
        if odd(a[i]) {
            i = i + 1;
        } else {
            j = j - 1;
            let temp_i = a[i];
            let temp_j = a[j];
            a.set(i, temp_j);
            a.set(j, temp_i);
        }
    }
}
// </vc-code>

}
fn main() {}