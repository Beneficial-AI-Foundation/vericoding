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
/* helper modified by LLM (iteration 5): bounds of min */
proof fn min_ub(a: int, b: int)
    ensures
        min(a, b) <= a,
{
    proof {
        reveal(min);
        if a <= b {
            assert(min(a, b) == a);
            assert(min(a, b) <= a);
        } else {
            assert(min(a, b) == b);
            assert(min(a, b) <= a);
        }
    }
}

/* helper modified by LLM (iteration 5): bounds of min */
proof fn min_lb(a: int, b: int)
    ensures
        min(a, b) <= b,
{
    proof {
        reveal(min);
        if a <= b {
            assert(min(a, b) == a);
            assert(min(a, b) <= b);
        } else {
            assert(min(a, b) == b);
            assert(min(a, b) <= b);
        }
    }
}

/* helper modified by LLM (iteration 5): relate integer min to usize min */
proof fn min_int_as_usize(a: int, b: int)
    requires
        0 <= a, 0 <= b,
    ensures
        (if (a as usize) <= (b as usize) { (a as usize) } else { (b as usize) }) == min(a, b) as usize,
{
    proof {
        reveal(min);
        if a <= b {
            assert(min(a, b) == a);
            assert(a as usize <= b as usize);
            assert((if (a as usize) <= (b as usize) { a as usize } else { b as usize }) == a as usize);
            assert(a as usize == min(a, b) as usize);
        } else {
            assert(min(a, b) == b);
            assert(b as usize <= a as usize);
            assert((if (a as usize) <= (b as usize) { a as usize } else { b as usize }) == b as usize);
            assert(b as usize == min(a, b) as usize);
        }
    }
}

/* helper modified by LLM (iteration 5): existence of 'a' implies count_a >= 1 */
proof fn count_a_exists_ge1(s: Seq<char>)
    requires
        exists|i: int| 0 <= i < s.len() && s[i] == 'a',
    ensures
        count_a(s) >= 1,
    decreases s.len(),
{
    proof {
        reveal(count_a);
        choose |idx| { 0 <= idx && idx < s.len() && s[idx] == 'a' };
        if s.len() == 0 {
            // impossible due to the exists precondition
            assert(false);
        } else {
            if idx == 0 {
                // first character is 'a'
                assert(s[0] == 'a');
                assert(count_a(s) == (if s[0] == 'a' { 1 as int } else { 0 as int }) + count_a(s.subrange(1, s.len() as int)));
                assert(count_a(s) >= 1);
            } else {
                // idx >= 1, so there is an 'a' in the tail
                assert(0 <= idx - 1 && idx - 1 < s.subrange(1, s.len() as int).len());
                assert(s.subrange(1, s.len() as int)[idx - 1] == 'a');
                // apply induction on the tail
                count_a_exists_ge1(s.subrange(1, s.len() as int));
                assert(count_a(s.subrange(1, s.len() as int)) >= 1);
                if s[0] == 'a' {
                    assert(count_a(s) == 1 + count_a(s.subrange(1, s.len() as int)));
                    assert(count_a(s) >= 2);
                } else {
                    assert(count_a(s) == count_a(s.subrange(1, s.len() as int)));
                    assert(count_a(s) >= 1);
                }
            }
        }
    }
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
/* code modified by LLM (iteration 5): compute runtime count with usize and return min in usize */
{
    let n: usize = s.len();
    let mut i: usize = 0;
    let mut cnt: usize = 0;
    while i < n
        invariant
            0 <= i as int,
            i as int <= n as int,
            cnt as int == count_a(s@.subrange(0, i as int)),
        decreases n - i
    {
        match s.get(i) {
            Option::Some(c) => {
                if *c == 'a' {
                    cnt = cnt + 1;
                }
            }
            Option::None => {}
        }
        i = i + 1;
    }
    // safe because valid_input guarantees at least one 'a', and thus cnt >= 1
    let two_cnt_minus_one: usize = 2 * cnt - 1;
    let result: usize = if two_cnt_minus_one <= n { two_cnt_minus_one } else { n };
    proof {
        // from the loop invariant and loop exit, cnt equals the spec count
        assert(i == n);
        assert(cnt as int == count_a(s@.subrange(0, i as int)));
        assert(cnt as int == count_a(s@));
        // existence of 'a' implies count_a >= 1 (use helper)
        count_a_exists_ge1(s@);
        assert(count_a(s@) >= 1);
        // non-negativity needed for the lemma
        assert(0 <= 2 * (cnt as int) - 1);
        assert(0 <= n as int);
        // use lemma to relate integer min to usize min
        min_int_as_usize(2 * (cnt as int) - 1, n as int);
        // simplify casts to match computed result
        assert((2 * (cnt as int) - 1) as usize == two_cnt_minus_one);
        assert((n as int) as usize == n);
        // conclude the ensured equality
        assert(result == min(2 * count_a(s@) - 1, s@.len() as int) as usize);
    }
    result
}

// </vc-code>


}

fn main() {}