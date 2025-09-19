// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn min_second_value_first(s: &Vec<Vec<i8>>) -> (first_of_min_second: i8)
    requires 
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> s@[i].len() >= 2,
    ensures 
        exists|i: int| 0 <= i < s.len() && first_of_min_second as int == s@[i]@[0] as int && 
            (forall|j: int| 0 <= j < s.len() ==> s@[i]@[1] as int <= s@[j]@[1] as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}