use vstd::prelude::*;

verus! {

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
fn sum_proof(s: Seq<int>, n: nat, k: nat)
    requires
        k <= n,
        n <= s.len(),
    ensures
        sum(s, n) == sum(s.subrange(0, k as int), k) + sum(s.subrange(k as int, n as int), (n - k) as nat),
    decreases n - k
{
    if n == k {
        assert(sum(s.subrange(k as int, n as int), (n - k) as nat) == sum(s.subrange(k as int, k as int), 0));
        assert(sum(s.subrange(k as int, n as int), (n - k) as nat) == 0) by {
            if (n - k) == 0 {
                assert(sum(s.subrange(k as int, n as int), (n - k) as nat) == 0);
            }
        }
    } else if k == 0 {
        assert(sum(s.subrange(0, k as int), k) == sum(s.subrange(0, 0), 0)) by {
            if k == (0 as nat) {
                assert(sum(s.subrange(0, k as int), k) == 0);
            }
        }
        assert(sum(s.subrange(0, k as int), k) == 0);
        assert(sum(s.subrange(k as int, n as int), (n - k) as nat) == sum(s, n));
    } else {
        assert(sum(s, n) == s[0] + sum(s.subrange(1, s.len() as int), (n - 1) as nat));
        proof {
            sum_proof(s.subrange(1, s.len() as int), (n - 1) as nat, (k - 1) as nat);
        }
        assert(sum(s.subrange(1, s.len() as int), (n - 1) as nat) == sum(s.subrange(1, k as int), (k - 1) as nat) + sum(s.subrange(k as int, n as int), (n - k) as nat));
    }
}
// </vc-helpers>

// <vc-spec>
fn below_zero(ops: Seq<int>) -> (result: bool)
    ensures result <==> exists|n: nat| n <= ops.len() && sum(ops, n) < 0
// </vc-spec>
// <vc-code>
{
    let mut current_sum: int = 0int;
    let mut found_below_zero: bool = false;

    let mut i: nat = 0nat;
    while i < ops.len()
        invariant
            0 <= i,
            i <= ops.len(),
            current_sum == sum(ops, i),
            found_below_zero <==> (exists|k: nat| k <= i && sum(ops, k) < 0),
    {
        current_sum = current_sum + ops.index(i);
        proof {
            sum_proof(ops, (i + 1) as nat, i);
        }
        assert(sum(ops, (i + 1) as nat) == sum(ops, i) + sum(ops.subrange(i as int, (i + 1) as int), 1 as nat));
        assert(sum(ops.subrange(i as int, (i + 1) as int), 1 as nat) == ops.index(i));
        assert(current_sum == sum(ops, (i + 1) as nat));

        if current_sum < 0int {
            found_below_zero = true;
        }
        i = i + 1;
    }
    found_below_zero
}
// </vc-code>

fn main() {
}

}