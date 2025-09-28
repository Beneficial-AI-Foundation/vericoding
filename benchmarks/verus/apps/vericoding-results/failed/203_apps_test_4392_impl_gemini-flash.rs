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
/* helper modified by LLM (iteration 5): The `as int` cast used in the `map_values` closure (`x: i8 | x as int`) inside the ensures clause of `can_sort` was a verification bug. This cast is not required for `i8` values in an exec context as `i8` implements `PartialOrd` and `Ord` traits directly, and comparisons with `i8` values are inherently allowed. The helper `bubble_sort_modified` relies on elements being `int`s for its spec, thus this helper remains the same but the function `can_sort` will be modified to cast at the start only for the specification related to `int`s. */
spec fn bubble_sort_modified(s: Seq<int>, allowed: Seq<bool>) -> Seq<int>
    decreases s.len()
{
    if s.len() <= 1 {
        s
    } else {
        bubble_sort_helper_modified(s, s.len() as nat, allowed)
    }
}

spec fn bubble_sort_helper_modified(s: Seq<int>, passes: nat, allowed: Seq<bool>) -> Seq<int>
    decreases passes
{
    if passes == 0 {
        s
    } else {
        bubble_sort_helper_modified(bubble_pass_modified(s, allowed), (passes - 1) as nat, allowed)
    }
}

spec fn bubble_pass_modified(s: Seq<int>, allowed: Seq<bool>) -> Seq<int>
    decreases s.len()
{
    if s.len() <= 1 {
        s
    } else {
        bubble_pass_helper_modified(s, 0, allowed)
    }
}

spec fn bubble_pass_helper_modified(s: Seq<int>, pos: nat, allowed: Seq<bool>) -> Seq<int>
    decreases if pos <= s.len() { s.len() - pos } else { 0 }
{
    if pos >= s.len() || pos >= s.len() - 1 {
        s
    } else if allowed[pos] && allowed[(pos + 1) as int] && s[pos as int] > s[(pos + 1) as int] {
        bubble_pass_helper_modified(s.update(pos as int, s[(pos + 1) as int]).update((pos + 1) as int, s[pos as int]), pos + 1, allowed)
    } else {
        bubble_pass_helper_modified(s, pos + 1, allowed)
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
/* code modified by LLM (iteration 5): The main change is in the `result == is_sorted()` line where `is_sorted` should be called with `a@.map_values(|x: i8| x as int)` for the ghost context. Another error noticed was in the `decreases` clause for the outer while loop, `n` is `usize` so it needs casting to `int`. Also the `invariant` for the inner `while` loop has a condition `allowed_pos` that uses `i` and `k` as `int`s in the `allowed_pos@[]` indexing so it needs casting to `int` and not `usize`. It also now checks if the array `a` is equal to the result of `bubble_sort_modified`. */
{
    let n = a.len();
    let mut swapped: bool = true;

    while swapped
        invariant
            0 <= n,
            a.len() == n,
            allowed_pos.len() == n,
            a@.map_values(|x: i8| x as int).to_multiset() == old(a)@.map_values(|x: i8| x as int).to_multiset(),

            forall|k: int| 0 <= k && k < n && !allowed_pos@[k] ==> a@ [k] == old(a)@[k],

            swapped == false ==> a@.map_values(|x: i8| x as int) == bubble_sort_modified(old(a)@.map_values(|x: i8| x as int), allowed_pos@),

        decreases n as int
    {
        swapped = false;
        let mut i: usize = 1;
        while i < n
            invariant
                0 < n,
                1 <= i,
                i <= n,
                a.len() == n,
                allowed_pos.len() == n,
                a@.map_values(|x: i8| x as int).to_multiset() == old(a)@.map_values(|x: i8| x as int).to_multiset(),

                forall|k: int| 0 <= k && k < n && !allowed_pos@[k] ==> a@[k] == old(a)@[k],

                forall|k: int| 0 <= k && k < (i as int) - 1 && allowed_pos@[k as int] && allowed_pos@[(k+1) as int] ==> a@[(k) as int] <= a@[(k+1) as int],

            decreases n - i
        {
            if allowed_pos[i] && allowed_pos[i - 1] {
                if a[i] < a[i - 1] {
                    let temp = a[i];
                    a.set(i, a[i - 1]);
                    a.set(i - 1, temp);
                    swapped = true;
                }
            }
            i = i + 1;
        }
    }
    
    is_sorted(a@.map_values(|x: i8| x as int))
}
// </vc-code>


}

fn main() {}