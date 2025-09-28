// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn all_even(a: Seq<int>) -> bool {
    forall|i: int| 0 <= i < a.len() ==> a[i] % 2 == 0
}

spec fn has_odd(a: Seq<int>) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i] % 2 == 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): [fix compilation error: incorrect modulo function call] */
fn has_odd_helper(a: &Vec<i8>) -> (res: bool)
    ensures res <==> has_odd(a@.map(|i, x| x as int)),
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a@ == old(a)@,
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < (i as int) ==> (a@[k] as int) % 2 != 1,
        decreases a.len() - i
    {
        if (a[i] as int) % 2 == 1 {
            return true;
        }
        i = i + 1;
    }
    false
}

proof fn lemma_has_odd_implies_not_all_even(s: Seq<int>)
    requires
        has_odd(s),
    ensures
        !all_even(s),
{
    let i = choose |i: int| 0 <= i < s.len() && s[i] % 2 == 1;
    assert(s[i] % 2 != 0);
    assert(!all_even(s));
}

/* helper modified by LLM (iteration 4): [fix compilation error: incorrect import path] */
proof fn lemma_not_has_odd_implies_all_even(s: Seq<int>)
    requires
        !has_odd(s),
    ensures
        all_even(s),
{
    use vstd::arithmetic::div_mod::lemma_mod_range;
    assert forall|i: int| 0 <= i < s.len() implies s[i] % 2 == 0 by {
        lemma_mod_range(s[i], 2);
        assert(s[i] % 2 != 1);
    }
    assert(all_even(s));
}
// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>) -> (result: &'static str)
    ensures 
        (result == "Second") <==> all_even(a@.map(|i: int, x: i8| x as int)),
        (result == "First") <==> has_odd(a@.map(|i: int, x: i8| x as int)),
        result == "First" || result == "Second",
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): [logic unchanged, relying on fixed helpers] */
    let ghost a_seq = a@.map(|i: int, x: i8| x as int);
    if has_odd_helper(&a) {
        proof {
            assert(has_odd(a_seq)); 
            lemma_has_odd_implies_not_all_even(a_seq);
            assert(!all_even(a_seq));
        }
        return "First";
    } else {
        proof {
            assert(!has_odd(a_seq));
            lemma_not_has_odd_implies_all_even(a_seq);
            assert(all_even(a_seq));
        }
        return "Second";
    }
}
// </vc-code>


}

fn main() {}