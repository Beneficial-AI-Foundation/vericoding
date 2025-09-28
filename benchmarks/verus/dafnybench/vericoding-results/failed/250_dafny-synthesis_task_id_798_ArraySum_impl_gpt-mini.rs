use vstd::prelude::*;

verus! {

spec fn sum_to(a: &[i32], n: int) -> int
    recommends 0 <= n <= a.len()
    decreases n
{
    if n <= 0 { 0 } else { sum_to(a, n - 1) + a[n - 1] }
}

// <vc-helpers>
proof fn lemma_sum_to_succ(a: &[i32], n: int)
    requires 0 <= n && n + 1 <= a.len()
    ensures sum_to(a, n + 1) == sum_to(a, n) + (a[n as usize] as int)
    decreases n
{
    if n == 0 {
        assert(sum_to(a, 1) == sum_to(a, 0) + (a[0usize] as int));
    } else {
        lemma_sum_to_succ(a, n - 1);
        assert(sum_to(a, n + 1) == sum_to(a, n) + (a[n as usize] as int));
    }
}
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &[i32]) -> (result: i32)
    ensures result == sum_to(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
    let mut i: int = 0;
    let mut s: int = 0;
    while i < a.len() as int
        invariant { 0 <= i && i <= a.len() as int }
        invariant { s == sum_to(a, i) }
        decreases { a.len() as int - i }
    {
        let v: i32 = a[i as usize];
        proof {
            lemma_sum_to_succ(a, i);
        }
        assert(s + (v as int) == sum_to(a, i + 1));
        s = s + (v as int);
        i = i + 1;
    }
    s as i32
}
// </vc-code>

fn main() {
}

}