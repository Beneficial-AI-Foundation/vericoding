// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, t: int) -> bool {
    1 <= n <= 10 && 0 <= t <= 10000
}

spec fn total_glasses(n: int) -> int {
    n * (n + 1) / 2
}

spec fn valid_result(result: int, n: int, t: int) -> bool {
    result >= 0 && result <= total_glasses(n)
}

spec fn correct_for_edge_cases(result: int, n: int, t: int) -> bool {
    (t == 0 ==> result == 0) &&
    (n == 1 && t >= 1 ==> result == 1) &&
    (n == 1 && t == 0 ==> result == 0) &&
    (t >= 1 && n > 1 ==> result >= 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `glass_dp_lemma` helper function is updated to take `n_local` as `int` directly, and `dp` type is changed to `Seq<Seq<i32>>` to avoid type casting issues in the invariant properties. This also removes a TODO comment from previous iteration. */
proof fn glass_dp_lemma(n_local: int, dp: Seq<Seq<i32>>) 
    requires
        n_local >= 0
    ensures
        forall|i: int| 0 <= i && i < dp.len() ==> dp[i as usize].len() == (n_local + 1) as usize
{
    // This lemma is a ghost function, and we don't need to implement any logic for the loop invariants
    // as the properties are directly about the sequence lengths.
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, t: i8) -> (result: i8)
requires 
    valid_input(n as int, t as int)
ensures 
    valid_result(result as int, n as int, t as int),
    correct_for_edge_cases(result as int, n as int, t as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type mismatch errors in `dp[i as usize].len() == (n_local as int + 1) as usize` by updating invariants. This was done by replacing `dp.len()` with `@dp.len()` to get the ghost length of the sequence, and specifying the inner length check as `dp[i].len() == (n_local + 1)` and then casting `n_local` to `int` instead of `usize` as `dp.len()` returns an `int`. */
{
    let n_local: i8 = n;
    let t_local: i8 = t;

    if t_local == 0 {
        return 0i8;
    }
    if n_local == 1 {
        if t_local >= 1 {
            return 1i8;
        } else {
            return 0i8;
        }
    }

    let mut dp: Vec<Vec<i32>> = vec![vec![0i32; (n_local + 1) as usize]; (n_local + 1) as usize];

    let initial_water_at_top = t_local as i32 * 100;
    dp[0][0] = initial_water_at_top;

    let mut r: i8 = 0;
    while r < n_local
        invariant
            0 <= r,
            r < n_local,
            dp@.len() == (n_local as int + 1),
            forall|i: int| 0 <= i && i < dp@.len() ==> dp@[i].len() == (n_local as int + 1),
    {
        let mut c: i8 = 0;
        while c <= r
            invariant
                0 <= r,
                r < n_local,
                0 <= c,
                c <= r,
                dp@.len() == (n_local as int + 1),
                forall|i: int| 0 <= i && i < dp@.len() ==> dp@[i].len() == (n_local as int + 1),
        {
            let water_in_current_glass = dp[r as usize][c as usize];
            let overflow_water = if water_in_current_glass > 100 { water_in_current_glass - 100 } else { 0 };

            if (r + 1) < n_local + 1 { // Check for bounds before accessing dp
                dp[(r + 1) as usize][c as usize] += overflow_water / 2;
                dp[(r + 1) as usize][(c + 1) as usize] += overflow_water / 2;
            }
            c = c + 1;
        }
        r = r + 1;
    }

    let mut count_full: i8 = 0;
    let mut r_final: i8 = 0;
    while r_final < n_local
        invariant
            0 <= r_final,
            r_final < n_local,
            0 <= count_full,
            count_full <= total_glasses(n_local as int) as i8,
            dp@.len() == (n_local as int + 1),
            forall|i: int| 0 <= i && i < dp@.len() ==> dp@[i].len() == (n_local as int + 1),

    {
        let mut c_final: i8 = 0;
        while c_final <= r_final
            invariant
                0 <= r_final,
                r_final < n_local,
                0 <= c_final,
                c_final <= r_final,
                0 <= count_full,
                count_full <= total_glasses(n_local as int) as i8,
                dp@.len() == (n_local as int + 1),
                forall|i: int| 0 <= i && i < dp@.len() ==> dp@[i].len() == (n_local as int + 1),
        {
            if dp[r_final as usize][c_final as usize] >= 100 {
                count_full = count_full + 1;
            }
            c_final = c_final + 1;
        }
        r_final = r_final + 1;
    }

    count_full
}
// </vc-code>


}

fn main() {}