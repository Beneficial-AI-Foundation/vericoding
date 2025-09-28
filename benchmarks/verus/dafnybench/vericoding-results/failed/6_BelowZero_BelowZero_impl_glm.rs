use vstd::prelude::*;

verus! {

/* 
HumanEvalX 3
You're given a list of deposit and withdrawal operations on a bank account that starts with zero balance. 
Your task is to detect if at any point the balance of account falls below zero, and at that point function 
should return True. Otherwise it should return False.
*/

spec fn sum(s: Seq<int>, n: nat) -> int
    recommends n <= s.len()
    decreases n
{
    if s.len() == 0 || n == 0 {
        0
    } else {
        s[0] + sum(s.subrange(1, s.len() as int), (n - 1) as nat)
    }
}

// <vc-helpers>
proof fn sum_subrange_add(s: Seq<int>, i: int, j: int, k: int)
    requires 0 <= i <= j <= k <= s.len()
    ensures sum(s.subrange(i, k), (j - i) as nat) + sum(s.subrange(j, k), (k - j) as nat) == sum(s.subrange(i, k), (k - i) as nat)
    decreases k - j
{
    if j == k {
        assert(sum(s.subrange(i, k), (j - i) as nat) == sum(s.subrange(i, k), (k - i) as nat));
    } else {
        vstd::calc! {
            sum(s.subrange(i, k), (j - i) as nat) + sum(s.subrange(j, k), (k - j) as nat);
            == { sum(s.subrange(j, k), (k - j) as nat) }
            sum(s.subrange(i, k), (j - i) as nat) + s[j] + sum(s.subrange(j + 1, k), (k - j - 1) as nat);
            == { assert(s.subrange(i, k).subrange(j - i, k - i) == s.subrange(j, k)); }
            sum(s.subrange(i, k).subrange(0, j - i), (j - i) as nat) + s.subrange(i, k)[j - i] + sum(s.subrange(i, k).subrange(j - i + 1, k - i), (k - j - 1) as nat);
            == { sum(s.subrange(i, k), (j - i + 1) as nat) }
            sum(s.subrange(i, k), (j - i + 1) as nat) + sum(s.subrange(i, k).subrange(j - i + 1, k - i), (k - j - 1) as nat);
            == { sum_subrange_add(s.subrange(i, k), 0, j - i + 1, k - i) }
            sum(s.subrange(i, k), (k - i) as nat);
        }
    }
}

proof fn sum_step(s: Seq<int>, i: nat)
    requires i < s.len()
    ensures sum(s, (i+1) as nat) == sum(s, i as nat) + s[i]
{
    sum_subrange_add(s, 0, i, i+1);
    let s1 = s.subrange(0, i+1);
    vstd::calc! {
        sum(s, i+1);
        == { assert(s1 == s.subrange(0, i+1)); }
        sum(s1, i+1);
        == { sum_subrange_add(s, 0, i, i+1) }
        sum(s1, i) + sum(s1.subrange(i, i+1), 1);
        == { assert(s1.subrange(0, i) == s.subrange(0, i)); }
        sum(s, i) + sum(s1.subrange(i, i+1), 1);
        == { assert(s1.subrange(i, i+1) == Seq::new(1, |j| s[i])); }
        sum(s, i) + s[i];
    }
}
// </vc-helpers>

// <vc-spec>
fn below_zero(ops: Seq<int>) -> (result: bool)
    ensures result <==> exists|n: nat| n <= ops.len() && sum(ops, n) < 0
// </vc-spec>
// <vc-code>
{
    let mut running_sum = 0;
    for i in 0..ops.len()
        invariant
            0 <= i <= ops.len(),
            running_sum == sum(ops, i as nat)
    {
        proof {
            sum_step(ops, i as nat);
        }
        running_sum = running_sum + ops[i];
        if running_sum < 0 {
            proof {
                assert(sum(ops, (i+1) as nat) < 0);
            }
            return true;
        }
    }
    return false;
}
// </vc-code>

fn main() {}

}