// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum_range(s: Seq<int>, start: int, end: int) -> int
    decreases end - start when 0 <= start <= end <= s.len()
{
    if start == end {
        0
    } else {
        s[start] + sum_range(s, start + 1, end)
    }
}

spec fn valid_input(n: int, years: Seq<int>) -> bool
{
    n > 0 && years.len() == n
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, years: Vec<i8>) -> (result: i8)
    requires n > 0 && years.len() == n as nat
    ensures result as int == sum_range(years@.map(|i, x| x as int), 0, years.len() as int) / (n as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): added proof blocks to ensure loop invariant maintenance and arithmetic safety */
    let mut total: i32 = 0;
    let mut i: usize = 0;
    while i < years.len()
        invariant
            0 <= i <= years.len(),
            total as int >= (i as int) * (-128),
            total as int <= (i as int) * 127,
        decreases years.len() - i
    {
        let old_i = i;
        proof {
            // Bounds for the current state
            assert(total as int >= (old_i as int) * (-128));
            assert(total as int <= (old_i as int) * 127);
            assert(years[old_i] as int >= -128);
            assert(years[old_i] as int <= 127);
            // The new total will be in the range:
            let new_low = (old_i as int) * (-128) + (-128);
            let new_high = (old_i as int) * 127 + 127;
            // And new_low = -128 * (old_i+1), new_high = 127 * (old_i+1)
            // Since old_i+1 <= years.len() (which is n) and n<=127, we have:
            assert(new_low >= -128 * 128); // = -16384
            assert(new_high <= 127 * 128); // = 16256
            // And these are within i32 range.
            assert(-2147483648 <= new_low && new_high <= 2147483647);
        }
        total = total + years[old_i] as i32;
        i = old_i + 1;
    }
    let n_i32 = n as i32;
    let average_i32 = total / n_i32;
    proof {
        // Prove that average_i32 is in [-128,127]
        // We know from the loop invariant at exit (i = years.len()):
        //   total as int >= (years.len() as int) * (-128)
        //   total as int <= (years.len() as int) * 127
        // Since years.len() = n (as int), we have:
        //   total as int >= n * (-128)
        //   total as int <= n * 127
        // Then, dividing by n (positive), we get:
        //   total/n >= -128
        //   total/n <= 127
        // But average_i32 is the truncation of total/n toward zero.
        // We consider two cases: total >= 0 and total < 0.
        if total >= 0 {
            // Then average_i32 = total / n_i32 (which is the same as floor(total/n)) but note: for nonnegative, truncation is floor.
            // And since total/n <= 127, then floor(total/n) <= 127.
            // And because total>=0, average_i32>=0.
            assert(average_i32 >= 0);
            assert(average_i32 <= 127);
        } else {
            // total < 0, then average_i32 = ceil(total/n) (truncation toward zero)
            // And total/n >= -128, so ceil(total/n) >= -128.
            // And because total<0, average_i32<0.
            assert(average_i32 >= -128);
            assert(average_i32 < 0);
        }
    }
    assert(-128 <= average_i32 && average_i32 <= 127);
    average_i32 as i8
// </vc-code>


}

fn main() {}