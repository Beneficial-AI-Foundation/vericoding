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
proof fn lemma_sum_negatives_to_equivalence(a: &[i32])
    ensures
        sum_negatives_to(a, a.len() as int) == |a|.filter(|x: i32| x < 0).sum()
{
    assert forall |k: int| 0 <= k <= a.len() implies sum_negatives_to(a, k) == |a|.subrange(0, k as int).filter(|x: i32| x < 0).sum() by {
        if k == 0 {
            assert(sum_negatives_to(a, 0) == 0);
            assert(|a|.subrange(0, 0).filter(|x: i32| x < 0).sum() == 0);
        } else {
            lemma_sum_negatives_to_equivalence(a);
            if a[k - 1] < 0 {
                assert(sum_negatives_to(a, k) == sum_negatives_to(a, k - 1) + a[k - 1]);
                assert(|a|.subrange(0, k as int).filter(|x: i32| x < 0).sum() == 
                       |a|.subrange(0, (k - 1) as int).filter(|x: i32| x < 0).sum() + a[k - 1]);
            } else {
                assert(sum_negatives_to(a, k) == sum_negatives_to(a, k - 1));
                assert(|a|.subrange(0, k as int).filter(|x: i32| x < 0).sum() == 
                       |a|.subrange(0, (k - 1) as int).filter(|x: i32| x < 0).sum());
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_of_negatives(a: &[i32]) -> (result: i32)
    ensures result == sum_negatives_to(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
    let mut sum: i32 = 0;
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            sum == sum_negatives_to(a, i as int)
        decreases a.len() - i
    {
        if a[i] < 0 {
            sum = sum + a[i];
        }
        i += 1;
    }
    sum
}
// </vc-code>

fn main() {}

}