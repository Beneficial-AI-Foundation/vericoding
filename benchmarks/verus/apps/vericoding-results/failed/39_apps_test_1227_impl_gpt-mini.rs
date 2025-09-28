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
/* helper modified by LLM (iteration 5): runtime digit counting helper using i8 locals and loop invariants */
fn runtime_count_non_zero_digits(mut x: i8) -> (result: i8)
    requires
        x as int >= 0,
    ensures
        result as int == count_non_zero_digits(x as int),
{
    let orig: i8 = x;
    let mut t: i8 = x;
    let mut cnt: i8 = 0;
    while t > 0
        invariant
            0 <= cnt as int,
            cnt as int + count_non_zero_digits(t as int) == count_non_zero_digits(orig as int),
        decreases t as int
    {
        if t % 10 != 0 {
            cnt = cnt + 1;
        }
        t = t / 10;
    }
    cnt
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
{
    /* code modified by LLM (iteration 5): iterate numbers and count using runtime helper */
    let mut i: i8 = 1;
    let mut cnt: i8 = 0;
    while i <= n
        invariant
            1 <= i as int && i as int <= n as int + 1,
            cnt as int == count_range(n as int, k as int, 1, (i as int) - 1),
        decreases n as int - i as int + 1
    {
        let c: i8 = runtime_count_non_zero_digits(i);
        if c == k {
            cnt = cnt + 1;
        }
        i = i + 1;
    }
    cnt
}
// </vc-code>


}

fn main() {}