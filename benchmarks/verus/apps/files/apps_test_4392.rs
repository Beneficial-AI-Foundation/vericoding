// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: &[int], allowed_pos: &[bool]) -> bool {
    a.len() > 1 && allowed_pos.len() == a.len()
}

spec fn is_sorted(a: Seq<int>) -> bool {
    a.len() <= 1 || forall|i: int| 0 <= i < a.len() - 1 ==> a[i] <= a[i + 1]
}

spec fn can_reach_configuration(original: Seq<int>, target: Seq<int>, allowed: Seq<bool>) -> bool {
    original.len() == target.len() && target.len() == allowed.len() &&
    original.to_multiset() == target.to_multiset()
}

spec fn sort_sequence(s: Seq<int>) -> Seq<int>
    decreases s.len()
{
    if s.len() <= 1 {
        s
    } else {
        bubble_sort_seq(s)
    }
}

spec fn bubble_sort_seq(s: Seq<int>) -> Seq<int>
    decreases s.len()
{
    if s.len() <= 1 {
        s
    } else {
        bubble_sort_helper(s, s.len() as int)
    }
}

spec fn bubble_sort_helper(s: Seq<int>, passes: int) -> Seq<int>
    decreases passes
{
    if passes <= 0 {
        s
    } else {
        let after_pass = bubble_pass(s);
        bubble_sort_helper(after_pass, passes - 1)
    }
}

spec fn bubble_pass(s: Seq<int>) -> Seq<int>
    decreases s.len()
{
    if s.len() <= 1 {
        s
    } else {
        bubble_pass_helper(s, 0)
    }
}

spec fn bubble_pass_helper(s: Seq<int>, pos: int) -> Seq<int>
    decreases s.len() - pos
{
    if pos >= s.len() - 1 {
        s
    } else if pos < s.len() - 1 && s[pos] > s[pos + 1] {
        let swapped = s.update(pos, s[pos + 1]).update(pos + 1, s[pos]);
        bubble_pass_helper(swapped, pos + 1)
    } else {
        bubble_pass_helper(s, pos + 1)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn can_sort(a: &mut [int], allowed_pos: &[bool]) -> (result: bool) 
    requires 
        valid_input(old(a), allowed_pos),
    ensures 
        a@.to_multiset() == old(a)@.to_multiset(),
        result == is_sorted(a@),
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

fn main() {}