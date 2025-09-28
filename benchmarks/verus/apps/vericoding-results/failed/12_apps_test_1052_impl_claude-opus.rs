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

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires valid_input(n as int, k as int)
    ensures result as int == factorial(n as int) - sum_binomial_derangement(n as int, k as int, 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed factorial invariant, overflow checks, and array bounds */
    let mut factorials: Vec<i32> = Vec::new();
    factorials.push(1);
    let mut i: i32 = 1;
    while i <= n as i32
        invariant
            1 <= i <= n as i32 + 1,
            factorials.len() == i as nat,
            forall|j: int| 0 <= j < i ==> factorials@[j] as int == factorial(j),
        decreases n as i32 - i + 1
    {
        let prev = factorials[(i - 1) as usize];
        assert(0 <= i - 1 < factorials.len());
        assert(factorials@[i - 1] as int == factorial(i - 1));
        assert(factorial(i as int) == i * factorial(i - 1));
        factorials.push(prev * i);
        assert(factorials@[i as int] as int == factorial(i as int));
        i = i + 1;
    }

    let mut derangements: Vec<i32> = Vec::new();
    derangements.push(0);
    if n >= 1 {
        derangements.push(0);
    }
    if n >= 2 {
        derangements.push(1);
        let mut j: i32 = 3;
        while j <= n as i32
            invariant
                3 <= j <= n as i32 + 1,
                derangements.len() == j as nat,
                forall|m: int| 0 <= m < j ==> derangements@[m] as int == derangement(m),
            decreases n as i32 - j + 1
        {
            assert(0 <= j - 1 < derangements.len());
            assert(0 <= j - 2 < derangements.len());
            let d1 = derangements[(j - 1) as usize];
            let d2 = derangements[(j - 2) as usize];
            assert(derangements@[j - 1] as int == derangement(j - 1));
            assert(derangements@[j - 2] as int == derangement(j - 2));
            assert(derangement(j as int) == (j - 1) * (derangement(j - 1) + derangement(j - 2)));
            derangements.push((j - 1) * (d1 + d2));
            assert(derangements@[j as int] as int == derangement(j as int));
            j = j + 1;
        }
    }

    let mut sum: i32 = 0;
    let mut idx: i32 = 0;
    assert(n >= k);
    assert(k >= 1);
    assert(n - k >= 0);
    while idx < (n as i32 - k as i32)
        invariant
            0 <= idx <= n as i32 - k as i32,
            factorials.len() == (n as nat + 1),
            derangements.len() >= (n as nat + 1),
            forall|j: int| 0 <= j <= n ==> factorials@[j] as int == factorial(j),
            forall|j: int| 0 <= j <= n ==> derangements@[j] as int == derangement(j),
            sum as int == sum_binomial_derangement(n as int, k as int, 0) - sum_binomial_derangement(n as int, k as int, idx as int),
        decreases n as i32 - k as i32 - idx
    {
        assert(0 <= n as int < factorials.len());
        assert(0 <= idx as int < factorials.len());
        assert(0 <= (n as i32 - idx) as int <= n as int);
        assert(0 <= (n as i32 - idx) as int < factorials.len());
        assert(0 <= (n as i32 - idx) as int < derangements.len());
        let binom = factorials[n as usize] / (factorials[idx as usize] * factorials[(n as i32 - idx) as usize]);
        assert(binom as int == binomial(n as int, idx as int));
        sum = sum + binom * derangements[(n as i32 - idx) as usize];
        idx = idx + 1;
    }

    assert(sum as int == sum_binomial_derangement(n as int, k as int, 0));
    assert(0 <= n as int < factorials.len());
    (factorials[n as usize] - sum) as i8
}
// </vc-code>


}

fn main() {}