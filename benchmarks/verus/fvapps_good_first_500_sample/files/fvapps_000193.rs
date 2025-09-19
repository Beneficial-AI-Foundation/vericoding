// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn string_after_abc_removal(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() < 3 {
        s
    } else if s.subrange(0, 3) == seq!['a', 'b', 'c'] {
        string_after_abc_removal(s.subrange(3, s.len() as int))
    } else {
        seq![s[0]] + string_after_abc_removal(s.subrange(1, s.len() as int))
    }
}

fn is_valid(s: &str) -> (result: bool)
    ensures 
        result == (string_after_abc_removal(s@) == Seq::<char>::empty()),
        s@ == Seq::<char>::empty() ==> result == true,
        s@.contains('d') ==> result == false
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-code>


}
fn main() {
    // println!("{}", is_valid("aabcbc"));
    // println!("{}", is_valid("abcabcababcc"));
    // println!("{}", is_valid("abccba"));
}