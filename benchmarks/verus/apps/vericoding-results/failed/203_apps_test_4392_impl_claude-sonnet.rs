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
/* helper modified by LLM (iteration 2): removed ghost types and fixed undefined variable */
fn check_can_swap(a: &Vec<i8>, pos: usize, allowed_pos: &[bool]) -> bool
    requires
        pos < a.len(),
        pos + 1 < a.len(),
        allowed_pos.len() == a.len(),
    ensures
        result == (allowed_pos[pos] && allowed_pos[pos + 1]),
{
    allowed_pos[pos] && allowed_pos[pos + 1]
}

fn bubble_sort_with_constraints(a: &mut Vec<i8>, allowed_pos: &[bool]) -> bool
    requires
        a.len() > 1,
        allowed_pos.len() == a.len(),
    ensures
        a@.map_values(|x: i8| x as ghost int).to_multiset() == old(a)@.map_values(|x: i8| x as ghost int).to_multiset(),
{
    let mut swapped = true;
    let mut can_complete_sort = true;
    
    while swapped
        invariant
            a@.map_values(|x: i8| x as ghost int).to_multiset() == old(a)@.map_values(|x: i8| x as ghost int).to_multiset(),
            a.len() == allowed_pos.len(),
            a.len() > 1,
    {
        swapped = false;
        let mut i = 0;
        
        while i < a.len() - 1
            invariant
                i <= a.len() - 1,
                a@.map_values(|x: i8| x as ghost int).to_multiset() == old(a)@.map_values(|x: i8| x as ghost int).to_multiset(),
                a.len() == allowed_pos.len(),
                a.len() > 1,
        {
            if a[i] > a[i + 1] {
                if check_can_swap(a, i, allowed_pos) {
                    let temp = a[i];
                    a.set(i, a[i + 1]);
                    a.set(i + 1, temp);
                    swapped = true;
                } else {
                    can_complete_sort = false;
                    break;
                }
            }
            i += 1;
        }
        
        if !can_complete_sort {
            break;
        }
    }
    
    proof {
        let ghost_seq = a@.map_values(|x: i8| x as ghost int);
        can_complete_sort && is_sorted(ghost_seq)
    }
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
    /* code modified by LLM (iteration 2): directly call helper function */
    let result = bubble_sort_with_constraints(a, allowed_pos);
    result
}
// </vc-code>


}

fn main() {}