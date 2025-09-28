// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int) -> bool {
    4 <= n <= 1000 && 1 <= k <= 4 && k < n
}

spec fn factorial(n: int) -> int
    decreases n
{
    if n <= 1 { 1 } else { n * factorial(n - 1) }
}

spec fn derangement(n: int) -> int
    decreases n
{
    if n <= 1 { 0 }
    else if n == 2 { 1 }
    else { (n - 1) * (derangement(n - 1) + derangement(n - 2)) }
}

spec fn binomial(n: int, k: int) -> int {
    if k > n { 0 }
    else if k == 0 || k == n { 1 }
    else { factorial(n) / (factorial(k) * factorial(n - k)) }
}

spec fn sum_binomial_derangement(n: int, k: int, i: int) -> int
    decreases n - k - i
{
    if i >= n - k { 0 }
    else { binomial(n, i) * derangement(n - i) + sum_binomial_derangement(n, k, i + 1) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): derangement number modulo 256 using u16 */
fn derangement_mod(n: u16) -> u16
{
    if n == 0 { 1 }
    else if n == 1 { 0 }
    else if n == 2 { 1 }
    else {
        let mut d0: u16 = 1; // D0
        let mut d1: u16 = 0; // D1
        let mut d2: u16 = 1; // D2
        let mut current: u16 = 0;
        if n <= 2 {
            return if n==0 { d0 } else if n==1 { d1 } else { d2 };
        }
        let mut i: u16 = 3;
        while i <= n {
            current = ((i-1) * (d1 + d2)) % 256;
            d0 = d1;
            d1 = d2;
            d2 = current;
            i = i + 1;
        }
        current
    }
}

/* helper modified by LLM (iteration 5): binomial coefficient modulo 256 using u16, fixed vector creation */
fn binomial_mod(n: u16, k: u16) -> u16
{
    if k > n {
        return 0;
    }
    let mut dp = Vec::new();
    let mut i: u16 = 0;
    while i <= n {
        dp.push(0);
        i = i + 1;
    }
    dp[0] = 1;
    let mut i: u16 = 1;
    while i <= n {
        let mut j: u16 = i;
        while j > 0 {
            let new_val = (dp[j as usize] + dp[(j-1) as usize]) % 256;
            dp[j as usize] = new_val;
            j = j - 1;
        }
        i = i + 1;
    }
    dp[k as usize]
}

/* helper modified by LLM (iteration 4): sum of binomial*derangement modulo 256 using u16 */
fn sum_binomial_derangement_mod(n: u16, k: u16) -> u16
{
    let mut sum: u16 = 0;
    let mut i: u16 = 0;
    while i < n - k {
        let term = (binomial_mod(n, i) * derangement_mod(n - i)) % 256;
        sum = (sum + term) % 256;
        i = i + 1;
    }
    sum
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires valid_input(n as int, k as int)
    ensures result as int == factorial(n as int) - sum_binomial_derangement(n as int, k as int, 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): use u16 to avoid int in non-ghost code, and i32 for modulo arithmetic */
    let n_u16 = n as u16;
    let k_u16 = k as u16;
    let factorial_n_mod = if n_u16 <= 7 {
        let mut fact: u16 = 1;
        let mut i: u16 = 1;
        while i <= n_u16 {
            fact = (fact * i) % 256;
            i = i + 1;
        }
        fact
    } else {
        0
    };
    let sum = sum_binomial_derangement_mod(n_u16, k_u16);
    let result_i32 = (factorial_n_mod as i32 - sum as i32) % 256;
    let result = if result_i32 < 0 { result_i32 + 256 } else { result_i32 };
    result as i8
}
// </vc-code>


}

fn main() {}