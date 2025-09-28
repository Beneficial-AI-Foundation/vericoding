// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: Seq<int>) -> bool {
    forall|i: int| 0 <= i < a.len() ==> a[i] > 0
}

spec fn count_factors_of_two(n: int) -> int
    decreases n when n > 0
{
    if n > 0 && n % 2 == 0 { 1 + count_factors_of_two(n / 2) }
    else { 0 }
}

spec fn sum_factors(a: Seq<int>, i: int) -> int
    decreases a.len() - i when 0 <= i <= a.len()
{
    if 0 <= i < a.len() && (forall|j: int| 0 <= j < a.len() ==> a[j] > 0) {
        count_factors_of_two(a[i]) + sum_factors(a, i + 1)
    } else if i == a.len() {
        0
    } else {
        0
    }
}

spec fn max_operations(a: Seq<int>) -> int {
    if valid_input(a) { sum_factors(a, 0) } else { 0 }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed count<=6 invariant and changed decreases measure to match spec */
fn count_exec(original_n: i8) -> (count: i8)
    requires original_n > 0,
    ensures
        count >= 0,
        count as int == count_factors_of_two(original_n as int),
{
    let mut n = original_n;
    let mut count: u8 = 0;
    while n % 2 == 0
        invariant 
            n > 0,
            count as int + count_factors_of_two(n as int) == count_factors_of_two(original_n as int),
        decreases n when n > 0
    {
        n = n / 2;
        count += 1;
    }
    count as i8
}
// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>) -> (result: i8)
    requires 
        valid_input(a@.map(|i, x| x as int)),
    ensures 
        result >= 0,
        result as int == max_operations(a@.map(|i, x| x as int)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): changed total to u8, added invariant to bound total by 127, and fixed loop invariant */
    let mut i = 0usize;
    let n = a.len();
    let mut total: u8 = 0;
    while i < n
        invariant 
            i <= n,
            n == a.len(),
            total as int + sum_factors(a@.map(|j, x| x as int), i as int) == sum_factors(a@.map(|j, x| x as int), 0),
            total + 6 * (n - i) <= 127,
        decreases (n - i) as int
    {
        let x = a[i];
        let count = count_exec(x);
        total = total + count as u8;
        i += 1;
    }
    total as i8
}
// </vc-code>


}

fn main() {}