// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn common_divisors(a: int, b: int) -> Set<int>
{
  Set::new(|d: int| 1 <= d <= a && a % d == 0 && b % d == 0)
}

spec fn valid_input(a: int, b: int, k: int) -> bool
{
  a > 0 && b > 0 && k >= 1 && common_divisors(a, b).len() >= k
}

spec fn is_kth_largest_common_divisor(a: int, b: int, k: int, result: int) -> bool
{
  valid_input(a, b, k) ==> (
    result > 0 &&
    a % result == 0 && b % result == 0 &&
    common_divisors(a, b).contains(result) &&
    Set::new(|d: int| common_divisors(a, b).contains(d) && d > result).len() == (k - 1)
  )
}
// </vc-preamble>

// <vc-helpers>
spec fn gcd(a: int, b: int) -> int
    decreases a + b
{
    if a == b {
        a
    } else if a > b {
        gcd(a - b, b)
    } else {
        gcd(a, b - a)
    }
}

fn collect_divisors(n: i8) -> (result: Vec<i8>)
    requires n > 0
    ensures
        forall |i: int| 0 <= i < result.len() ==> result@[i] > 0,
        forall |i: int| 0 <= i < result.len() ==> (n as int) % (result@[i] as int) == 0,
        forall |d: int| 1 <= d <= (n as int) && (n as int) % d == 0 ==> exists |i: int| 0 <= i < result.len() && result@[i] == d
{
    /* helper modified by LLM (iteration 5): removed requires/ensures from spec function */
    let mut divisors: Vec<i8> = Vec::new();
    let mut i = 1;
    while i <= n
        invariant
            1 <= i <= n + 1,
            forall |j: int| 0 <= j < divisors.len() ==> divisors@[j] > 0,
            forall |j: int| 0 <= j < divisors.len() ==> (n as int) % (divisors@[j] as int) == 0,
            forall |d: int| 1 <= d < i && (n as int) % d == 0 ==> exists |j: int| 0 <= j < divisors.len() && divisors@[j] == d
    {
        if n % i == 0 {
            divisors.push(i);
        }
        i = i + 1;
    }
    divisors
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, k: i8) -> (result: i8)
  requires valid_input(a as int, b as int, k as int)
  ensures is_kth_largest_common_divisor(a as int, b as int, k as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix compilation error by removing requires/ensures from spec function */
    let mut gcd_val = if a < b { a } else { b };
    while gcd_val > 0
        invariant
            gcd_val >= 0,
            gcd_val <= a,
            gcd_val <= b
    {
        if a % gcd_val == 0 && b % gcd_val == 0 {
            break;
        }
        gcd_val = gcd_val - 1;
    }
    
    let divisors = collect_divisors(gcd_val);
    
    let mut sorted_divisors = divisors;
    let mut i = 0;
    while i < sorted_divisors.len()
        invariant
            0 <= i <= sorted_divisors.len(),
            forall |j: int| 0 <= j < sorted_divisors.len() ==> sorted_divisors@[j] > 0,
            forall |j: int| 0 <= j < sorted_divisors.len() ==> (a as int) % (sorted_divisors@[j] as int) == 0,
            forall |j: int| 0 <= j < sorted_divisors.len() ==> (b as int) % (sorted_divisors@[j] as int) == 0
    {
        let mut j = i + 1;
        while j < sorted_divisors.len()
            invariant
                i < j <= sorted_divisors.len(),
                forall |l: int| 0 <= l < sorted_divisors.len() ==> sorted_divisors@[l] > 0
        {
            if sorted_divisors[j] > sorted_divisors[i] {
                let temp = sorted_divisors[i];
                sorted_divisors.set(i, sorted_divisors[j]);
                sorted_divisors.set(j, temp);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    sorted_divisors[(k - 1) as usize]
}
// </vc-code>


}

fn main() {}