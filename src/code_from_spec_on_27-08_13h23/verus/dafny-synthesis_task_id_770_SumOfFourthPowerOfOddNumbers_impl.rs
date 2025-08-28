use vstd::prelude::*;

verus! {

// <vc-helpers>
fn compute_fourth_power(x: i32) -> i32
    ensures x * x * x * x == result
{
    x * x * x * x
}

proof fn prove_sum_formula(n: i32)
    requires n > 0,
    ensures n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15 == {
        let mut sum: i32 = 0;
        let mut k: i32 = 1;
        while k <= n
            invariant
                1 <= k <= n + 1,
                sum == {
                    let mut s: i32 = 0;
                    let mut i: i32 = 1;
                    while i < k
                        invariant
                            1 <= i <= k,
                            s == {
                                let mut temp_s: i32 = 0;
                                let mut temp_i: i32 = 1;
                                while temp_i < i {
                                    if temp_i % 2 == 1 {
                                        temp_s = temp_s + compute_fourth_power(temp_i);
                                    }
                                    temp_i = temp_i + 1;
                                }
                                temp_s
                            },
                    {
                        if i % 2 == 1 {
                            s = s + compute_fourth_power(i);
                        }
                        i = i + 1;
                    }
                    s
                },
        {
            if k % 2 == 1 {
                sum = sum + compute_fourth_power(k);
            }
            k = k + 1;
        }
        sum
    }
{
    let mut sum: i32 = 0;
    let mut k: i32 = 1;
    while k <= n
        invariant
            1 <= k <= n + 1,
            sum == {
                let mut s: i32 = 0;
                let mut i: i32 = 1;
                while i < k
                    invariant
                        1 <= i <= k,
                        s == {
                            let mut temp_s: i32 = 0;
                            let mut temp_i: i32 = 1;
                            while temp_i < i {
                                if temp_i % 2 == 1 {
                                    temp_s = temp_s + compute_fourth_power(temp_i);
                                }
                                temp_i = temp_i + 1;
                            }
                            temp_s
                        },
                {
                    if i % 2 == 1 {
                        s = s + compute_fourth_power(i);
                    }
                    i = i + 1;
                }
                s
            },
    {
        if k % 2 == 1 {
            sum = sum + compute_fourth_power(k);
        }
        k = k + 1;
    }
    assert(sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn sum_of_fourth_power_of_odd_numbers(n: i32) -> (sum: i32)
    requires n > 0,
    ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15,
// </vc-spec>
// </vc-spec>

// <vc-code>
fn sum_of_fourth_power_of_odd_numbers(n: i32) -> (sum: i32)
    requires n > 0,
    ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15,
{
    let mut sum: i32 = 0;
    let mut k: i32 = 1;
    while k <= n
        invariant
            1 <= k <= n + 1,
            sum == {
                let mut s: i32 = 0;
                let mut i: i32 = 1;
                while i < k
                    invariant
                        1 <= i <= k,
                        s == {
                            let mut temp_s: i32 = 0;
                            let mut temp_i: i32 = 1;
                            while temp_i < i {
                                if temp_i % 2 == 1 {
                                    temp_s = temp_s + compute_fourth_power(temp_i);
                                }
                                temp_i = temp_i + 1;
                            }
                            temp_s
                        },
                {
                    if i % 2 == 1 {
                        s = s + compute_fourth_power(i);
                    }
                    i = i + 1;
                }
                s
            },
    {
        if k % 2 == 1 {
            sum = sum + compute_fourth_power(k);
        }
        k = k + 1;
    }
    proof {
        prove_sum_formula(n);
    }
    sum
}
// </vc-code>

fn main() {}

}