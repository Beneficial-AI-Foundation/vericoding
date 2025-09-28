// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_non_zero_digits(n: int) -> int
    decreases n when n >= 0
{
    if n == 0 { 0 }
    else if n % 10 == 0 { count_non_zero_digits(n / 10) }
    else { 1 + count_non_zero_digits(n / 10) }
}

spec fn count_numbers_with_k_non_zero_digits(n: int, k: int) -> int
{
    count_range(n, k, 1, n)
}

spec fn count_range(n: int, k: int, start: int, end: int) -> int
    decreases if end < start { 0int } else { end - start + 1 }
{
    if start > end { 0 }
    else if count_non_zero_digits(start) == k { 
        1 + count_range(n, k, start + 1, end)
    } else { 
        count_range(n, k, start + 1, end)
    }
}

spec fn valid_input(n: int, k: int) -> bool
{
    n >= 1 && k >= 1 && k <= 3
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added lemmas for step properties, bounds, and range-step; rewrote helper to reason in int domain and prevent overflow */
proof fn lemma_count_non_zero_digits_step(m: int)
    requires
        m >= 0,
    ensures
        m % 10 == 0 ==> count_non_zero_digits(m) == count_non_zero_digits(m / 10),
        m % 10 != 0 ==> count_non_zero_digits(m) == 1 + count_non_zero_digits(m / 10),
{
    if m == 0 {
        assert(m % 10 == 0);
        assert(count_non_zero_digits(m) == 0);
        assert(count_non_zero_digits(m / 10) == count_non_zero_digits(0));
    } else {
        if m % 10 == 0 {
            assert(count_non_zero_digits(m) == count_non_zero_digits(m / 10));
        } else {
            assert(count_non_zero_digits(m) == 1 + count_non_zero_digits(m / 10));
        }
    }
}

/* helper modified by LLM (iteration 2): bound for numbers < 10 */
proof fn lemma_cnz_upper_lt10(n: int)
    requires
        0 <= n,
        n < 10,
    ensures
        count_non_zero_digits(n) <= 1,
{
    if n == 0 {
        assert(count_non_zero_digits(n) == 0);
    } else {
        lemma_count_non_zero_digits_step(n);
        assert(n / 10 == 0);
        if n % 10 == 0 {
            assert(count_non_zero_digits(n) == count_non_zero_digits(n / 10));
            assert(count_non_zero_digits(n) == 0);
        } else {
            assert(count_non_zero_digits(n) == 1 + count_non_zero_digits(n / 10));
            assert(count_non_zero_digits(n / 10) == 0);
            assert(count_non_zero_digits(n) == 1);
        }
    }
}

/* helper modified by LLM (iteration 2): bound for numbers < 100 using lt10 */
proof fn lemma_cnz_upper_lt100(n: int)
    requires
        0 <= n,
        n < 100,
    ensures
        count_non_zero_digits(n) <= 2,
{
    if n == 0 {
        assert(count_non_zero_digits(n) == 0);
    } else {
        lemma_count_non_zero_digits_step(n);
        // n < 100 => n/10 < 10
        assert(n / 10 < 10) by {
            assert(0 <= n);
            assert(n <= 99);
        };
        lemma_cnz_upper_lt10(n / 10);
        if n % 10 == 0 {
            assert(count_non_zero_digits(n) == count_non_zero_digits(n / 10));
            assert(count_non_zero_digits(n) <= 1);
        } else {
            assert(count_non_zero_digits(n) == 1 + count_non_zero_digits(n / 10));
            assert(count_non_zero_digits(n / 10) <= 1);
            assert(count_non_zero_digits(n) <= 2);
        }
    }
}

/* helper modified by LLM (iteration 2): bound for numbers < 1000 using lt100 */
proof fn lemma_cnz_upper_lt1000(n: int)
    requires
        0 <= n,
        n < 1000,
    ensures
        count_non_zero_digits(n) <= 3,
{
    if n == 0 {
        assert(count_non_zero_digits(n) == 0);
    } else {
        lemma_count_non_zero_digits_step(n);
        // n < 1000 => n/10 < 100
        assert(n / 10 < 100) by {
            assert(0 <= n);
            assert(n <= 999);
        };
        lemma_cnz_upper_lt100(n / 10);
        if n % 10 == 0 {
            assert(count_non_zero_digits(n) == count_non_zero_digits(n / 10));
            assert(count_non_zero_digits(n) <= 2);
            assert(count_non_zero_digits(n) <= 3);
        } else {
            assert(count_non_zero_digits(n) == 1 + count_non_zero_digits(n / 10));
            assert(count_non_zero_digits(n / 10) <= 2);
            assert(count_non_zero_digits(n) <= 3);
        }
    }
}

/* helper modified by LLM (iteration 4): add explicit int literals (1int/0int) to avoid type inference error */
proof fn lemma_count_range_end_step(n: int, k: int, start: int, i: int)
    requires
        valid_input(n, k),
        1 <= start,
        start <= i,
        i <= n,
    ensures
        count_range(n, k, start, i) == count_range(n, k, start, i - 1) + (if count_non_zero_digits(i) == k { 1int } else { 0int }),
    decreases i - start + 1
{
    if start == i {
        assert(count_range(n, k, start, start - 1) == 0);
        if count_non_zero_digits(start) == k {
            assert(count_range(n, k, start, start) == 1 + count_range(n, k, start + 1, start));
            assert(count_range(n, k, start + 1, start) == 0);
        } else {
            assert(count_range(n, k, start, start) == count_range(n, k, start + 1, start));
            assert(count_range(n, k, start + 1, start) == 0);
        }
    } else {
        // Unfold both ends and use IH on (start + 1, i)
        if count_non_zero_digits(start) == k {
            assert(count_range(n, k, start, i) == 1 + count_range(n, k, start + 1, i));
            assert(count_range(n, k, start, i - 1) == 1 + count_range(n, k, start + 1, i - 1));
        } else {
            assert(count_range(n, k, start, i) == count_range(n, k, start + 1, i));
            assert(count_range(n, k, start, i - 1) == count_range(n, k, start + 1, i - 1));
        }
        lemma_count_range_end_step(n, k, start + 1, i);
        // From IH: count_range(start+1, i) == count_range(start+1, i-1) + indicator(i)
        if count_non_zero_digits(start) == k {
            assert(count_range(n, k, start, i) == 1 + (count_range(n, k, start + 1, i - 1) + (if count_non_zero_digits(i) == k { 1int } else { 0int })));
            assert(count_range(n, k, start, i - 1) + (if count_non_zero_digits(i) == k { 1int } else { 0int })
                   == (1 + count_range(n, k, start + 1, i - 1)) + (if count_non_zero_digits(i) == k { 1int } else { 0int }));
        } else {
            assert(count_range(n, k, start, i) == count_range(n, k, start + 1, i - 1) + (if count_non_zero_digits(i) == k { 1int } else { 0int }));
        }
    }
}

/* helper modified by LLM (iteration 4): added bound assertion for i8 and kept invariants; no exec-int vars */
fn count_non_zero_digits_i8(x: i8) -> (c: i8)
    requires
        x >= 0,
    ensures
        c as int == count_non_zero_digits(x as int),
        0 <= c as int,
{
    let mut m: i8 = x;
    let mut acc: i8 = 0;
    proof { assert(x as int <= 127); lemma_cnz_upper_lt1000(x as int); }
    while m != 0
        invariant
            m >= 0,
            0 <= acc as int,
            acc as int + count_non_zero_digits(m as int) == count_non_zero_digits(x as int),
        decreases m as int
    {
        proof { lemma_count_non_zero_digits_step(m as int); }
        if m % 10 == 0 {
            // acc unchanged
        } else {
            // Safe to increment acc since total count is at most 3
            proof {
                lemma_cnz_upper_lt1000(x as int);
                assert(count_non_zero_digits(x as int) <= 3);
                assert(count_non_zero_digits(m as int) >= 0);
                assert(acc as int <= count_non_zero_digits(x as int));
                assert((acc as int) + 1 <= 127);
            }
            acc = acc + 1;
        }
        m = m / 10;
    }
    // When m == 0: count_non_zero_digits(0) == 0, so acc == desired count
    acc
}
// </vc-helpers>

// <vc-spec>
fn count_numbers_with_exactly_k_non_zero_digits(n: i8, k: i8) -> (count: i8)
requires
    valid_input(n as int, k as int)
ensures
    count as int == count_numbers_with_k_non_zero_digits(n as int, k as int),
    count as int >= 0,
    count as int <= n as int
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): keep loop and invariants; use helper lemma for range step and i8 digit counter */
{
    let mut acc: i8 = 0;
    let mut i: i8 = 1;
    proof { assert(n as int <= 127); }
    while i <= n
        invariant
            valid_input(n as int, k as int),
            1 <= i as int,
            i as int <= n as int + 1,
            0 <= acc as int,
            acc as int <= i as int - 1,
            acc as int == count_range(n as int, k as int, 1, i as int - 1),
        decreases (n as int + 1) - i as int
    {
        assert(i >= 0);
        let c = count_non_zero_digits_i8(i);
        if c == k {
            proof {
                assert(i as int <= n as int);
                assert((acc as int) <= i as int - 1);
                assert(n as int <= 127);
                assert((acc as int) + 1 <= 127);
            }
            acc = acc + 1;
        }
        proof { lemma_count_range_end_step(n as int, k as int, 1, i as int); }
        i = i + 1;
    }
    assert(i as int == n as int + 1);
    acc
}
// </vc-code>


}

fn main() {}