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
proof fn sum_negatives_to_step(a: &[i32], n: int)
    requires 0 < n <= a.len()
    ensures
        a[n - 1] < 0 ==> sum_negatives_to(a, n) == sum_negatives_to(a, n - 1) + a[n - 1],
        !(a[n - 1] < 0) ==> sum_negatives_to(a, n) == sum_negatives_to(a, n - 1)
{
    reveal_with_fuel(sum_negatives_to, 1);
}
// </vc-helpers>

// <vc-spec>
fn sum_of_negatives(a: &[i32]) -> (result: i32)
    ensures result == sum_negatives_to(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while i < a.len()
        invariant 0 <= i as int <= a.len() as int && sum == sum_negatives_to(a, i as int)
    {
        let ai = a[i];
        proof {
            assert(0 <= i as int);
            assert(i < a.len());
        }
        let ghost n_i: int = i as int + 1;
        proof {
            assert(0 < n_i && n_i <= a.len() as int);
            assert(n_i - 1 == i as int);
            assert(0 <= n_i - 1 && n_i - 1 < a.len() as int);
            assert(a[n_i - 1] == a[i as int]);
            assert(a[i as int] == a[i]);
            assert(a[n_i - 1] == ai);
        }
        if ai < 0 {
            let s0 = sum;
            sum = sum + ai;
            proof {
                assert(s0 == sum_negatives_to(a, i as int));
                assert(n_i - 1 == i as int);
                assert(s0 == sum_negatives_to(a, n_i - 1));
                assert(a[n_i - 1] == ai);
                assert(sum == sum_negatives_to(a, n_i - 1) + a[n_i - 1]);
                sum_negatives_to_step(a, n_i);
                assert(a[n_i - 1] < 0);
                assert(sum == sum_negatives_to(a, n_i));
            }
        } else {
            proof {
                assert(a[n_i - 1] == ai);
                assert(!(a[n_i - 1] < 0));
                sum_negatives_to_step(a, n_i);
                assert(sum_negatives_to(a, n_i) == sum_negatives_to(a, n_i - 1));
                assert(sum == sum_negatives_to(a, n_i));
            }
        }
        i = i + 1;
        proof { assert(i as int == n_i); }
    }
    sum
}
// </vc-code>

fn main() {}

}