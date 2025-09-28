// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: Seq<int>, allowed_pos: Seq<bool>) -> bool {
    a.len() > 1 && allowed_pos.len() == a.len()
}

spec fn is_sorted(a: Seq<int>) -> bool
    decreases a.len()
{
    if a.len() <= 1 {
        true
    } else {
        a[0] <= a[1] && is_sorted(a.subrange(1, a.len() as int))
    }
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
        bubble_sort_helper(s, s.len() as nat)
    }
}

spec fn bubble_sort_helper(s: Seq<int>, passes: nat) -> Seq<int>
    decreases passes
{
    if passes == 0 {
        s
    } else {
        bubble_sort_helper(bubble_pass(s), (passes - 1) as nat)
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

spec fn bubble_pass_helper(s: Seq<int>, pos: nat) -> Seq<int>
    decreases if pos <= s.len() { s.len() - pos } else { 0 }
{
    if pos >= s.len() || pos >= s.len() - 1 {
        s
    } else if s[pos as int] > s[(pos + 1) as int] {
        bubble_pass_helper(s.update(pos as int, s[(pos + 1) as int]).update((pos + 1) as int, s[pos as int]), pos + 1)
    } else {
        bubble_pass_helper(s, pos + 1)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed ghost variable syntax */
proof fn adjacent_swap_preserves_multiset(v: Vec<i8>, i: int) -> ()
    requires 0 <= i < v.len() - 1
    ensures v@.update(i, v@[i+1]).update(i+1, v@[i]).to_multiset() == v@.to_multiset()
{
    let v1 = v@.update(i, v@[i+1]);
    let v2 = v1.update(i+1, v@[i]);
    assert(v2.to_multiset() =~= v@.to_multiset());
}
// </vc-helpers>

// <vc-spec>
fn can_sort(a: &mut Vec<i8>, allowed_pos: &[bool]) -> (result: bool)
    requires 
        valid_input(old(a)@.map_values(|x: i8| x as int), allowed_pos@),
    ensures 
        a@.map_values(|x: i8| x as int).to_multiset() == old(a)@.map_values(|x: i8| x as int).to_multiset(),
        result == is_sorted(a@.map_values(|x: i8| x as int)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed ghost variable declaration causing compilation error */
    let n = a.len();
    if n <= 1 {
        return true;
    }

    for pass in 0..n
        invariant
            a@.map_values(|x: i8| x as int).to_multiset() == old(a)@.map_values(|x: i8| x as int).to_multiset(),
        decreases n - pass
    {
        let mut swapped = false;
        for i in 0..n-1
            invariant
                a@.map_values(|x: i8| x as int).to_multiset() == old(a)@.map_values(|x: i8| x as int).to_multiset(),
            decreases n - 1 - i
        {
            if allowed_pos[i] && a[i] > a[i+1] {
                proof {
                    adjacent_swap_preserves_multiset(*a, i as int);
                }
                a.swap(i, i+1);
                swapped = true;
            }
        }
        if !swapped {
            break;
        }
    }

    // Check if the array is sorted
    for i in 0..n-1 {
        if a[i] > a[i+1] {
            return false;
        }
    }
    true
}
// </vc-code>


}

fn main() {}