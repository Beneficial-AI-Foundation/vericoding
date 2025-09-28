// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 3
}

spec fn count_excessive_positions(s: Seq<char>) -> int {
    count_excessive_positions_helper(s, 0, 0)
}

spec fn count_excessive_positions_helper(s: Seq<char>, pos: int, consecutive_x: int) -> int
    decreases s.len() - pos
{
    if pos >= s.len() {
        0
    } else {
        let new_consecutive_x = if s[pos] == 'x' { consecutive_x + 1 } else { 0 };
        let current_contribution: int = if new_consecutive_x > 2 { 1 } else { 0 };
        current_contribution + count_excessive_positions_helper(s, pos + 1, new_consecutive_x)
    }
}

spec fn consecutive_x_count(s: Seq<char>, pos: int) -> int
    decreases pos
{
    if pos == 0 {
        0
    } else if pos > 0 && pos <= s.len() && s[pos - 1] == 'x' {
        1 + consecutive_x_count(s, pos - 1)
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Unfold the recursive helper at an in-bounds index */
proof fn lemma_unfold_helper_index(s: Seq<char>, pos: int, consecutive_x: int)
    requires
        0 <= pos,
        pos < s.len(),
    ensures
        count_excessive_positions_helper(s, pos, consecutive_x)
            ==
        {
            let new_consecutive_x = if s[pos] == 'x' { consecutive_x + 1 } else { 0 };
            let current_contribution: int = if new_consecutive_x > 2 { 1 } else { 0 };
            current_contribution + count_excessive_positions_helper(s, pos + 1, new_consecutive_x)
        },
{
    reveal(count_excessive_positions_helper);
}

/* helper modified by LLM (iteration 2): Unfold the recursive helper at/after the end of the sequence */
proof fn lemma_unfold_helper_ge_len(s: Seq<char>, pos: int, consecutive_x: int)
    requires
        0 <= pos,
        pos >= s.len(),
    ensures
        count_excessive_positions_helper(s, pos, consecutive_x) == 0,
{
    reveal(count_excessive_positions_helper);
}

/* helper modified by LLM (iteration 2): Relate consecutive_x_count across an 'x' step */
proof fn lemma_consecutive_step_x(s: Seq<char>, pos: int)
    requires
        0 <= pos,
        pos < s.len(),
        s[pos] == 'x',
    ensures
        consecutive_x_count(s, pos + 1) == consecutive_x_count(s, pos) + 1,
{
    reveal(consecutive_x_count);
    assert(pos + 1 > 0);
    assert(pos + 1 <= s.len());
}

/* helper modified by LLM (iteration 2): Relate consecutive_x_count across a non-'x' step */
proof fn lemma_consecutive_step_notx(s: Seq<char>, pos: int)
    requires
        0 <= pos,
        pos < s.len(),
        s[pos] != 'x',
    ensures
        consecutive_x_count(s, pos + 1) == 0,
{
    reveal(consecutive_x_count);
    assert(pos + 1 > 0);
    assert(pos + 1 <= s.len());
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures 
        result >= 0,
        result as int <= s@.len(),
        result as int == count_excessive_positions(s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implement counting with a loop invariant tied to the spec and fix bounds issues */
    let n: usize = s.len();
    let mut i: usize = 0;
    let mut consec: usize = 0;
    let mut cnt: usize = 0;

    proof {
        assert(count_excessive_positions(s@) == count_excessive_positions_helper(s@, 0, 0));
        assert(consecutive_x_count(s@, 0) == 0);
    }

    while i < n
        invariant
            i <= n,
            consec as int == consecutive_x_count(s@, i as int),
            cnt as int + count_excessive_positions_helper(s@, i as int, consec as int) == count_excessive_positions(s@),
        decreases n - i
    {
        assert(i < n);
        assert(n == s.len());
        let ch = s[i];
        let gi: int = i as int;
        assert(0 <= gi);
        assert(s@.len() == n as int);
        assert(gi < s@.len());
        assert(s@[gi] == ch);

        let old_cnt: usize = cnt;
        let old_consec_int: int = consec as int;

        if ch == 'x' {
            consec = consec + 1;
        } else {
            consec = 0;
        }

        if consec > 2 {
            cnt = cnt + 1;
        }

        i = i + 1;

        proof {
            let new_i: int = gi + 1;
            let new_consec_int: int = if s@[gi] == 'x' { old_consec_int + 1 } else { 0 };
            let contrib: int = if new_consec_int > 2 { 1 } else { 0 };

            if s@[gi] == 'x' {
                lemma_consecutive_step_x(s@, gi);
            } else {
                lemma_consecutive_step_notx(s@, gi);
            }
            assert(consecutive_x_count(s@, new_i) == new_consec_int);
            assert(consec as int == new_consec_int);

            lemma_unfold_helper_index(s@, gi, old_consec_int);
            assert(
                count_excessive_positions_helper(s@, gi, old_consec_int)
                ==
                contrib + count_excessive_positions_helper(s@, new_i, new_consec_int)
            );

            if new_consec_int > 2 {
                assert(cnt as int == old_cnt as int + 1);
            } else {
                assert(cnt as int == old_cnt as int);
            }

            assert(
                old_cnt as int + count_excessive_positions_helper(s@, gi, old_consec_int)
                ==
                cnt as int + count_excessive_positions_helper(s@, new_i, new_consec_int)
            );
        }
    }

    proof {
        assert(i == n);
        assert(s@.len() == n as int);
        let pos: int = n as int;
        assert(pos >= s@.len());
        lemma_unfold_helper_ge_len(s@, pos, consec as int);
        assert(count_excessive_positions_helper(s@, pos, consec as int) == 0);
        assert(cnt as int == count_excessive_positions(s@));
    }

    assert(cnt <= n);

    let result: i8 = cnt as i8;
    result
}
// </vc-code>


}

fn main() {}