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
/* helper modified by LLM (iteration 5): define pairwise nondecreasing property over a sequence, and link it to is_sorted */
spec fn nondecreasing_pairs(s: Seq<int>) -> bool
    decreases s.len()
{
    if s.len() <= 1 {
        true
    } else {
        s[0] <= s[1] && nondecreasing_pairs(s.subrange(1, s.len() as int))
    }
}

/* helper modified by LLM (iteration 5): show equivalence between is_sorted and nondecreasing_pairs */
proof fn lemma_is_sorted_eq_pairs(s: Seq<int>)
    ensures
        is_sorted(s) == nondecreasing_pairs(s),
    decreases s.len()
{
    if s.len() <= 1 {
    } else {
        lemma_is_sorted_eq_pairs(s.subrange(1, s.len() as int));
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
    /* code modified by LLM (iteration 5): compute sorted by backward scan that matches recursive spec; no mutations */
    let n: usize = a.len();
    if n <= 1 {
        proof { lemma_is_sorted_eq_pairs(a@.map_values(|x: i8| x as int)); }
        return true;
    }
    let mut k: usize = n - 1;
    let mut ok: bool = true;
    while k > 0
        invariant
            n == a.len(),
            (k as int) <= (n as int) - 1,
            ok == nondecreasing_pairs(a@.map_values(|x: i8| x as int).subrange(k as int, n as int)),
        decreases (k as int)
    {
        let prev: int = a[k - 1] as int;
        let curr: int = a[k] as int;
        ok = (prev <= curr) && ok;
        k = k - 1;
    }
    proof {
        // subrange(0, len) equals the sequence itself
        assert(a@.map_values(|x: i8| x as int).subrange(0, n as int) == a@.map_values(|x: i8| x as int));
        lemma_is_sorted_eq_pairs(a@.map_values(|x: i8| x as int));
    }
    let result = ok;
    result
}
// </vc-code>


}

fn main() {}