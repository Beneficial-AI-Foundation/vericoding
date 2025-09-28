use vstd::prelude::*;

verus! {

spec fn sum_to(a: &[i32], n: int) -> int
    recommends 0 <= n <= a.len()
    decreases n
{
    if n <= 0 { 0 } else { sum_to(a, n - 1) + a[n - 1] }
}

// <vc-helpers>
proof fn sum_to_lemma(a: &[i32], k: int, m: int)
    requires 0 <= k <= m <= a.len()
    ensures sum_to(a, m) == sum_to(a, k) + sum_to(a.subslice(k as usize, m as usize), m - k)
    decreases m - k
{
    if k < m {
        sum_to_lemma(a, k, m - 1);
        proof {
            let slice = a.subslice(k as usize, m as usize);
            assert(slice.len() == (m - k) as usize);
        }
        assert(sum_to(a, m) == sum_to(a, m - 1) + a[(m - 1) as usize]);
    }
}

proof fn sum_to_single_element(a: &[i32], idx: int)
    requires 0 <= idx < a.len()
    ensures sum_to(a, idx + 1) == sum_to(a, idx) + a[idx as usize]
{
    if idx >= 0 {
        assert(sum_to(a, idx + 1) == sum_to(a, idx) + a[idx as usize]) by {
            reveal_with_fuel(sum_to, 2);
        };
    }
}

spec fn subslice(a: &[i32], start: usize, end: usize) -> &[i32]
    recommends 0 <= start <= end <= a.len()
    ensures result@ == a@.subrange(start as int, end as int)
{
    a
}
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &[i32]) -> (result: i32)
    ensures result == sum_to(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
    let mut total = 0;
    let mut i: usize = 0;
    let n = a.len();
    while i < n 
        invariant 
            0 <= i <= n,
            total == sum_to(a, i as int),
        decreases n - i
    {
        assert(i < n);
        let value = a[i];
        total = total + value;
        
        proof {
            sum_to_single_element(a, i as int);
        }
        
        i = i + 1;
    }
    total
}
// </vc-code>

fn main() {
}

}