use vstd::prelude::*;

verus! {

// <vc-helpers>
// Added helper to relate division and multiplication for even n.
fn lemma_div2_mul(n: nat)
    requires n % 2 == 0
    ensures n == (n / 2) * 2
{
    // standard div/mod identity: n == (n/2)*2 + n%2
    assert(n == (n / 2) * 2 + n % 2);
    assert(n % 2 == 0);
    assert((n / 2) * 2 + n % 2 == (n / 2) * 2);
    assert(n == (n / 2) * 2);
}
// </vc-helpers>

// <vc-spec>
fn pairwise_addition(a: &[i32]) -> (result: Vec<i32>)
    requires
        a.len() % 2 == 0,
    ensures
        result.len() == a.len() / 2,
        forall|i: int| 0 <= i < result.len() ==> result[i as int] == a[2*i] + a[2*i + 1],
// </vc-spec>
// <vc-code>
{
    let n: nat = a.len();
    let m: nat = n / 2;
    // use helper to know 2*m == n
    lemma_div2_mul(n);
    let mut result: Vec<i32> = Vec::with_capacity(m);
    let mut k: nat = 0;
    while k < m
        invariant k <= m;
        invariant result.len() == k;
        invariant forall|j: int| 0 <= j && j < k as int ==>
            #[trigger] result[j] == a[2*(j as nat)] + a[2*(j as nat) + 1];
        decreases m - k;
    {
        // prove indices are in bounds
        proof {
            assert(k < m);
            assert(2*k < 2*m);
            assert(2*k + 1 <= 2*m);
            assert(n == (n / 2) * 2);
            assert(m == n / 2);
            assert(2*m == n);
            assert(2*k + 1 <= n);
            assert((2*k + 1) % 2 == 1);
            assert(n % 2 == 0);
            assert(2*k + 1 != n);
            assert(2*k + 1 < n);
        }
        let idx: nat = k;
        let s: i32 = a[2*idx] + a[2*idx + 1];
        result.push(s);
        // show newly pushed element satisfies the invariant for index idx
        proof {
            assert(result.len() == idx + 1);
            assert(result[idx as int] == s);
            assert(result[idx as int] == a[2*idx] + a[2*idx + 1]);
        }
        k = k + 1;
    }
    result
}
// </vc-code>

fn main() {}

}