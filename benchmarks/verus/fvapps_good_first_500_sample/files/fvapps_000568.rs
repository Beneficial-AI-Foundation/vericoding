// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn string_has_no_ones(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] != '1'
}

spec fn string_starts_with_zero(s: Seq<char>) -> bool {
    s.len() > 0 && s[0] == '0'
}

spec fn string_all_ones(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> s[i] == '1'
}

fn count_inscribed_circles(s: &str) -> (result: usize)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>

}

fn main() {
    // let test1 = count_inscribed_circles("1110");
    // assert_eq!(test1, 1);
    
    // let test2 = count_inscribed_circles("0010");
    // assert_eq!(test2, 0);
    
    // let test3 = count_inscribed_circles("1001000");
    // assert_eq!(test3, 2);
}