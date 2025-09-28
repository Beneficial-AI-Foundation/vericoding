// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn count_a(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0 as int
    } else {
        (if s[0] == 'a' { 1 as int } else { 0 as int }) + count_a(s.subrange(1, s.len() as int))
    }
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 1 && exists|i: int| 0 <= i < s.len() && s[i] == 'a'
}

spec fn is_good_string(s: Seq<char>) -> bool {
    s.len() > 0 && count_a(s) > s.len() as int / 2
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): [removed nested proof block to fix compilation error] */
proof fn lemma_count_a_non_zero_if_contains_a(s: Seq<char>)
    requires
        exists|k: int| 0 <= k < s.len() && s[k] == 'a',
    ensures
        count_a(s) > 0,
    decreases s.len(),
{
    if s.len() > 0 {
        if s[0] == 'a' {
            assert(count_a(s) >= 1);
        } else {
            let s_rest = s.subrange(1, s.len() as int);
            let k = choose|k_idx: int| 0 <= k_idx < s.len() && s[k_idx] == 'a';
            assert(k > 0);
            let j = k - 1;
            assert(0 <= j < s_rest.len());
            assert(s_rest[j] == s[k]);
            assert(s_rest[j] == 'a');
            assert(exists|i: int| 0 <= i < s_rest.len() && s_rest[i] == 'a');
            
            lemma_count_a_non_zero_if_contains_a(s_rest);
            
            assert(count_a(s_rest) > 0);
            assert(count_a(s) == count_a(s_rest));
        }
    }
}

/* helper modified by LLM (iteration 3): [added type suffixes to fix type inference errors] */
proof fn lemma_count_a_append(s: Seq<char>, c: char)
    ensures
        count_a(s.push(c)) == count_a(s) + (if c == 'a' { 1int } else { 0int }),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        lemma_count_a_append(s.subrange(1, s.len() as int), c);
        assert(s.push(c).subrange(1, s.push(c).len() as int)
            =~= s.subrange(1, s.len() as int).push(c));
    }
}

/* helper modified by LLM (iteration 3): [added type suffixes to fix type inference errors] */
fn count_a_exec(s: &Vec<char>) -> (count: usize)
    ensures
        count as int == count_a(s@),
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s@.len() == s.len(),
            count as int == count_a(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        let c = s[i];
        proof {
            let sub_prev = s@.subrange(0, i as int);
            let sub_curr = s@.subrange(0, (i + 1) as int);
            assert(sub_curr =~= sub_prev.push(c));
            lemma_count_a_append(sub_prev, c);
            assert(count_a(sub_curr) == count_a(sub_prev) + if c == 'a' { 1int } else { 0int });
        }

        if c == 'a' {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: usize)
    requires 
        valid_input(s@),
    ensures 
        result >= 1,
        result <= s.len(),
        result == min(2 * count_a(s@) - 1, s.len() as int) as usize,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): [no change to logic, fixed helper compilation error] */
    let num_a_usize = count_a_exec(&s);

    proof {
        lemma_count_a_non_zero_if_contains_a(s@);
        assert(count_a(s@) > 0);
        assert(num_a_usize as int == count_a(s@));
        assert(num_a_usize >= 1);
    }
    
    let val1 = 2 * num_a_usize - 1;
    let len = s.len();

    if val1 <= len {
        val1
    } else {
        len
    }
}
// </vc-code>


}

fn main() {}