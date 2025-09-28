use vstd::prelude::*;

verus! {

spec fn sum_negatives_to(a: &[i32], n: int) -> int
    recommends 0 <= n <= a.len()
    decreases n
{
    if n == 0 { 
        0 
    } else if n > 0 && a[n - 1] < 0 { 
        sum_negatives_to(a, n - 1) + a[n - 1] 
    } else if n > 0 { 
        sum_negatives_to(a, n - 1) 
    } else {
        0
    }
}

// <vc-helpers>
proof fn lemma_sum_negatives_step(a: &[i32], i: int)
    requires 0 <= i && i < a.len() as int
    ensures sum_negatives_to(a, i + 1) == sum_negatives_to(a, i) + (if a[i as usize] < 0 { a[i as usize] } else { 0 })
{
    if a[i as usize] < 0 {
        assert(sum_negatives_to(a, i + 1) == sum_negatives_to(a, i) + a[i as usize]);
    } else {
        assert(sum_negatives_to(a, i + 1) == sum_negatives_to(a, i));
        assert(sum_negatives_to(a, i + 1) == sum_negatives_to(a, i) + 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_of_negatives(a: &[i32]) -> (result: i32)
    ensures result == sum_negatives_to(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
    let n: int = a.len() as int;
    let mut i: int = 0;
    let mut s: i32 = 0;
    while i < n
        invariant 0 <= i && i <= n;
        invariant s as int == sum_negatives_to(a, i);
        decreases n - i;
    {
        let ai: i32 = a[i as usize];
        proof {
            lemma_sum_negatives_step(a, i);
        }
        if ai < 0 {
            s = s + ai;
        }
        assert(s as int == sum_negatives_to(a, i + 1));
        i = i + 1;
    }
    s
}
// </vc-code>

fn main() {}

}