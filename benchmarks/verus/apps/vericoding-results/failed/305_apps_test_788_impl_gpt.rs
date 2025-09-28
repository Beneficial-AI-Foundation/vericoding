// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() == 7 && s[0] == 'A' && forall|i: int| 1 <= i < 7 ==> #[trigger] s[i] >= '0' && #[trigger] s[i] <= '9'
}

spec fn digit_sum(s: Seq<char>, start: int, end: int) -> int
    decreases end - start when 0 <= start <= end <= s.len()
{
    if start >= end {
        0
    } else {
        (s[start] as int - '0' as int) + digit_sum(s, start + 1, end)
    }
}

spec fn zero_count(s: Seq<char>, start: int, end: int) -> int
    decreases end - start when 0 <= start <= end <= s.len()
{
    if start >= end {
        0
    } else {
        (if s[start] == '0' { 1nat } else { 0nat }) as int + zero_count(s, start + 1, end)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): extension lemma for digit_sum over [a, b) with explicit case analysis */
proof fn lemma_digit_sum_extend(s: Seq<char>, a: int, b: int)
    requires
        0 <= a,
        a < b,
        b <= s.len(),
    ensures
        digit_sum(s, a, b) == digit_sum(s, a, b - 1) + (s[b - 1] as int - '0' as int),
    decreases b - a
{
    if a + 1 == b {
        assert(digit_sum(s, a, b) == (s[a] as int - '0' as int) + digit_sum(s, a + 1, b));
        assert(digit_sum(s, a + 1, b) == 0);
        assert(digit_sum(s, a, b) == (s[a] as int - '0' as int));
        assert(digit_sum(s, a, b - 1) == 0);
        assert(s[b - 1] == s[a]);
        assert(digit_sum(s, a, b) == digit_sum(s, a, b - 1) + (s[b - 1] as int - '0' as int));
    } else {
        lemma_digit_sum_extend(s, a + 1, b);
        assert(digit_sum(s, a, b) == (s[a] as int - '0' as int) + digit_sum(s, a + 1, b));
        assert(digit_sum(s, a, b - 1) == (s[a] as int - '0' as int) + digit_sum(s, a + 1, b - 1));
        assert(digit_sum(s, a + 1, b) == digit_sum(s, a + 1, b - 1) + (s[b - 1] as int - '0' as int));
        assert(digit_sum(s, a, b) == digit_sum(s, a, b - 1) + (s[b - 1] as int - '0' as int));
    }
}

/* helper modified by LLM (iteration 5): extension lemma for zero_count over [a, b) with explicit case analysis */
proof fn lemma_zero_count_extend(s: Seq<char>, a: int, b: int)
    requires
        0 <= a,
        a < b,
        b <= s.len(),
    ensures
        zero_count(s, a, b) == zero_count(s, a, b - 1) + (if s[b - 1] == '0' { 1 } else { 0 }),
    decreases b - a
{
    if a + 1 == b {
        assert(zero_count(s, a, b) == (if s[a] == '0' { 1nat } else { 0nat }) as int + zero_count(s, a + 1, b));
        assert(zero_count(s, a + 1, b) == 0);
        assert(zero_count(s, a, b) == (if s[a] == '0' { 1 } else { 0 }));
        assert(zero_count(s, a, b - 1) == 0);
        assert(s[b - 1] == s[a]);
        assert(zero_count(s, a, b) == zero_count(s, a, b - 1) + (if s[b - 1] == '0' { 1 } else { 0 }));
    } else {
        lemma_zero_count_extend(s, a + 1, b);
        assert(zero_count(s, a, b) == (if s[a] == '0' { 1nat } else { 0nat }) as int + zero_count(s, a + 1, b));
        assert(zero_count(s, a, b - 1) == (if s[a] == '0' { 1nat } else { 0nat }) as int + zero_count(s, a + 1, b - 1));
        assert(zero_count(s, a + 1, b) == zero_count(s, a + 1, b - 1) + (if s[b - 1] == '0' { 1 } else { 0 }));
        assert(zero_count(s, a, b) == zero_count(s, a, b - 1) + (if s[b - 1] == '0' { 1 } else { 0 }));
    }
}

/* helper modified by LLM (iteration 5): relate Vec indexing with its Seq view for a usize index */
proof fn lemma_vec_index_agrees_usize(s: &Vec<char>, i: usize)
    requires
        i < s.len(),
    ensures
        s@[i as int] == s[i],
{
}

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures result as int == digit_sum(s@, 1, 7) + 9 * zero_count(s@, 1, 7) + 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): remove problematic assert, use lemma to relate Vec and Seq indexing, and keep loop invariants */
    let mut i: usize = 1;
    let mut sum: i32 = 0;
    let mut zc: i32 = 0;

    while i < 7
        invariant
            valid_input(s@),
            s@.len() == 7,
            1 <= i as int,
            i as int <= 7,
            sum as int == digit_sum(s@, 1, i as int),
            zc as int == zero_count(s@, 1, i as int),
            0 <= sum as int,
            sum as int <= 9 * (i as int - 1),
            0 <= zc as int,
            zc as int <= i as int - 1,
        decreases 7 - (i as int)
    {
        let ch: char = s[i];
        proof {
            // Relate s@[i] to s[i]
            lemma_vec_index_agrees_usize(&s, i);
            assert(1 <= i as int);
            assert(s@[i as int] == ch);
            // From valid_input, digits are in ['0','9'] for indices 1..6
            assert('0' <= s@[i as int]);
            assert(s@[i as int] <= '9');
        }
        let d: i32 = (ch as i32) - ('0' as i32);
        let incr: i32 = if ch == '0' { 1 } else { 0 };

        let next_i: usize = i + 1;
        let next_sum: i32 = sum + d;
        let next_zc: i32 = zc + incr;

        proof {
            // d and incr ranges, and connection to spec characters
            assert(d as int == ch as int - '0' as int);
            assert(d as int == s@[i as int] as int - '0' as int);
            assert(0 <= d as int);
            assert(d as int <= 9);
            assert(incr as int == (if s@[i as int] == '0' { 1 } else { 0 }));
            assert(0 <= incr as int);
            assert(incr as int <= 1);

            // Extend specs to i+1
            lemma_digit_sum_extend(s@, 1, i as int + 1);
            lemma_zero_count_extend(s@, 1, i as int + 1);

            // Update equalities for invariants
            assert(next_sum as int == sum as int + d as int);
            assert(sum as int == digit_sum(s@, 1, i as int));
            assert(next_sum as int == digit_sum(s@, 1, i as int) + (s@[i as int] as int - '0' as int));
            assert(i as int + 1 == next_i as int);
            assert(next_sum as int == digit_sum(s@, 1, next_i as int));

            assert(next_zc as int == zc as int + (if s@[i as int] == '0' { 1 } else { 0 }));
            assert(next_zc as int == zero_count(s@, 1, next_i as int));

            // Bounds for sums and counts
            assert(0 <= next_sum as int);
            assert(0 <= next_zc as int);
            assert(sum as int + d as int <= 9 * (i as int - 1) + 9);
            assert(9 * (i as int - 1) + 9 == 9 * (i as int));
            assert(i as int == next_i as int - 1);
            assert(9 * (i as int) == 9 * (next_i as int - 1));
            assert(next_sum as int <= 9 * (next_i as int - 1));
            assert(zc as int + incr as int <= (i as int - 1) + 1);
            assert((i as int - 1) + 1 == i as int);
            assert(i as int == next_i as int - 1);
            assert(next_zc as int <= next_i as int - 1);
        }

        i = next_i;
        sum = next_sum;
        zc = next_zc;
    }

    proof { assert(i as int == 7); }
    proof {
        assert(sum as int == digit_sum(s@, 1, 7));
        assert(zc as int == zero_count(s@, 1, 7));
    }

    let total: i32 = sum + 9 * zc + 1;

    proof {
        assert(total as int == digit_sum(s@, 1, 7) + 9 * zero_count(s@, 1, 7) + 1);
        assert(0 <= sum as int);
        assert(0 <= zc as int);
        assert(i as int == 7);
        assert(sum as int <= 9 * (i as int - 1));
        assert(zc as int <= i as int - 1);
        assert(sum as int <= 9 * 6);
        assert(zc as int <= 6);
        assert(total as int <= 9 * 6 + 9 * 6 + 1);
        assert(9 * 6 + 9 * 6 + 1 == 109);
        assert(0 <= total as int);
        assert(total as int <= 127);
    }

    let res: i8 = total as i8;
    proof { assert(res as int == total as int); }
    res
}
// </vc-code>


}

fn main() {}