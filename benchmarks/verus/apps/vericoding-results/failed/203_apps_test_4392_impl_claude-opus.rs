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
    /* code modified by LLM (iteration 5): Added trigger annotations for quantifier */
    let n = a.len();
    
    if n <= 1 {
        return true;
    }
    
    let mut changed = true;
    let mut pass_count: usize = 0;
    
    while changed
        invariant
            a@.len() == old(a)@.len(),
            a@.map_values(|x: i8| x as int).to_multiset() == old(a)@.map_values(|x: i8| x as int).to_multiset(),
            allowed_pos@.len() == a@.len(),
            pass_count <= n,
        decreases n - pass_count
    {
        changed = false;
        let mut i: usize = 0;
        
        while i < n - 1
            invariant
                i <= n - 1,
                a@.len() == n,
                a@.map_values(|x: i8| x as int).to_multiset() == old(a)@.map_values(|x: i8| x as int).to_multiset(),
                allowed_pos@.len() == n,
            decreases n - 1 - i
        {
            if allowed_pos[i] && a[i] > a[i + 1] {
                let temp = a[i];
                a.set(i, a[i + 1]);
                a.set(i + 1, temp);
                changed = true;
            }
            i = i + 1;
        }
        
        if pass_count < n {
            pass_count = pass_count + 1;
        }
    }
    
    let mut sorted = true;
    let mut j: usize = 0;
    
    while j < n - 1
        invariant
            j <= n - 1,
            a@.len() == n,
            sorted == (forall|k: int| #[trigger] (a@.map_values(|x: i8| x as int)[k]) 0 <= k < j ==> a@.map_values(|x: i8| x as int)[k] <= a@.map_values(|x: i8| x as int)[k + 1]),
        decreases n - 1 - j
    {
        if a[j] > a[j + 1] {
            sorted = false;
        }
        j = j + 1;
    }
    
    sorted
}
// </vc-code>


}

fn main() {}