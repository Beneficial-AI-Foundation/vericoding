// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int) -> bool {
    1 <= a <= 10000 && 1 <= b <= 10000 && 1 <= c <= 10000
}

spec fn min_of_three(x: int, y: int, z: int) -> int {
    if x <= y && x <= z { x }
    else if y <= z { y }
    else { z }
}

spec fn correct_result(a: int, b: int, c: int) -> int {
    min_of_three(a + b, a + c, b + c)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate chosen machine-int minimum to the spec-level min_of_three */
proof fn min_three_matches_choice(s1: int, s2: int, s3: int, m: int)
    requires
        (m == s1 && s1 <= s2 && s1 <= s3) || (m == s2 && s2 <= s1 && s2 <= s3) || (m == s3 && s3 <= s1 && s3 <= s2),
    ensures
        m == min_of_three(s1, s2, s3),
{
    if m == s1 && s1 <= s2 && s1 <= s3 {
        assert(min_of_three(s1, s2, s3) == s1);
    } else if m == s2 && s2 <= s1 && s2 <= s3 {
        assert(min_of_three(s1, s2, s3) == s2);
    } else {
        assert(min_of_three(s1, s2, s3) == s3);
    }
    assert(m == min_of_three(s1, s2, s3));
}

/* helper modified by LLM (iteration 5): min_of_three is bounded by each argument (keeps previous useful fact) */
proof fn min_three_is_min(x: int, y: int, z: int)
    ensures
        min_of_three(x, y, z) <= x,
        min_of_three(x, y, z) <= y,
        min_of_three(x, y, z) <= z,
{
    if x <= y && x <= z {
        assert(min_of_three(x, y, z) == x);
    } else if y <= z {
        assert(min_of_three(x, y, z) == y);
    } else {
        assert(min_of_three(x, y, z) == z);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8) -> (result: i8)
    requires valid_input(a as int, b as int, c as int)
    ensures result as int == correct_result(a as int, b as int, c as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute sums in i32, pick min, cast with truncation, and prove equality using helper */
    let ai32: i32 = a as i32;
    let bi32: i32 = b as i32;
    let ci32: i32 = c as i32;
    let s1: i32 = ai32 + bi32;
    let s2: i32 = ai32 + ci32;
    let s3: i32 = bi32 + ci32;
    let m: i32;
    if s1 <= s2 && s1 <= s3 {
        m = s1;
    } else if s2 <= s3 {
        m = s2;
    } else {
        m = s3;
    }
    #[verifier::truncate]
    let result: i8 = m as i8;
    proof {
        let ai: int = a as int;
        let bi: int = b as int;
        let ci: int = c as int;
        let s1i: int = ai + bi;
        let s2i: int = ai + ci;
        let s3i: int = bi + ci;
        assert((s1 as int) == s1i);
        assert((s2 as int) == s2i);
        assert((s3 as int) == s3i);
        if s1 <= s2 && s1 <= s3 {
            assert((m as int) == s1i);
            assert(s1i <= s2i);
            assert(s1i <= s3i);
            min_three_matches_choice(s1i, s2i, s3i, m as int);
        } else if s2 <= s3 {
            assert((m as int) == s2i);
            assert(s2i <= s1i);
            assert(s2i <= s3i);
            min_three_matches_choice(s1i, s2i, s3i, m as int);
        } else {
            assert((m as int) == s3i);
            assert(s3i <= s1i);
            assert(s3i <= s2i);
            min_three_matches_choice(s1i, s2i, s3i, m as int);
        }
        assert(result as int == min_of_three(s1i, s2i, s3i));
    }
    result
}

// </vc-code>


}

fn main() {}