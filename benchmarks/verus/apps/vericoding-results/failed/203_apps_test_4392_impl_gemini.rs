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
/* helper modified by LLM (iteration 4): [no changes] */
proof fn lemma_is_sorted_equiv_forall(s: Seq<int>)
    ensures
        is_sorted(s) <==> (forall|i: int| 0 <= i < s.len() - 1 ==> s[i] <= s[i+1]),
    decreases s.len(),
{
    if s.len() > 1 {
        lemma_is_sorted_equiv_forall(s.subrange(1, s.len() as int));
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
    /* code modified by LLM (iteration 4): [fixed compilation error by implementing swap manually] */
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            a.len() == n,
            allowed_pos@.len() == n,
            a@.map_values(|v: i8| v as int).to_multiset() == old(a)@.map_values(|v: i8| v as int).to_multiset(),
        decreases n - i
    {
        let mut j: usize = 0;
        while j < n - 1
            invariant
                0 <= j <= n - 1,
                a.len() == n,
                allowed_pos@.len() == n,
                a@.map_values(|v: i8| v as int).to_multiset() == old(a)@.map_values(|v: i8| v as int).to_multiset(),
                i < n,
            decreases n - 1 - j
        {
            if allowed_pos[j] {
                let j_plus_1 = j + 1;
                if a[j] > a[j_plus_1] {
                    let tmp = a[j];
                    a.set(j, a[j_plus_1]);
                    a.set(j_plus_1, tmp);
                }
            }
            j = j + 1;
        }
        i = i + 1;
    }

    let mut k: usize = 0;
    while k < n - 1
        invariant
            0 <= k <= n - 1,
            a.len() == n,
            a@.map_values(|v: i8| v as int).to_multiset() == old(a)@.map_values(|v: i8| v as int).to_multiset(),
            forall|l: int| 0 <= l < k as int ==> (a@[l] as int) <= (a@[l+1] as int),
        decreases n - 1 - k
    {
        if a[k] > a[k + 1] {
            proof {
                lemma_is_sorted_equiv_forall(a@.map_values(|v: i8| v as int));
            }
            return false;
        }
        k = k + 1;
    }

    proof {
        lemma_is_sorted_equiv_forall(a@.map_values(|v: i8| v as int));
    }
    return true;
}
// </vc-code>


}

fn main() {}