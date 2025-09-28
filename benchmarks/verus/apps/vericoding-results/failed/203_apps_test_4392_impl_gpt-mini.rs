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
/* helper modified by LLM (iteration 5): convert Vec<i8> to Seq<int> */
spec fn vec_to_seq(a: &Vec<i8>) -> Seq<int> {
    a@.map_values(|x: i8| x as int)
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
    /* code modified by LLM (iteration 5): iterate checking adjacent pairs with loop invariant and decreases */
    let mut i: usize = 0;
    let mut res: bool = true;
    while i + 1 < a.len()
        invariant
            i <= a.len(),
            res == (forall |j: usize| j + 1 <= i ==> a[j] <= a[j + 1]),
        decreases a.len() - i
    {
        if a[i] > a[i + 1] {
            res = false;
            i = if a.len() == 0 { 0 } else { a.len() - 1 };
        } else {
            i = i + 1;
        }
    }
    let tracked tres = res;
    proof {
        // From loop exit we have i + 1 >= a.len()
        assert(i + 1 >= a.len());
        // Thus every adjacent index pair in the whole array satisfies j+1 <= i
        assert(forall |j: usize| j + 1 < a.len() ==> j + 1 <= i);
        // From the invariant we know res characterizes sortedness up to i
        assert(tres == (forall |j: usize| j + 1 <= i ==> a[j] <= a[j + 1]));
        // Combine the two to get full sortedness over all adjacent pairs
        assert(tres == (forall |j: usize| j + 1 < a.len() ==> a[j] <= a[j + 1]));
        // Which matches the definition of is_sorted on the sequence view
        assert(tres == is_sorted(vec_to_seq(a)));
    }
    res
}
// </vc-code>


}

fn main() {}