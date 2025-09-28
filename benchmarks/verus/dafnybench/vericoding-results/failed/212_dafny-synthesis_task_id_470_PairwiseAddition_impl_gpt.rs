use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_even_times_half_equals_self_usize(n: usize)
    requires
        n % 2 == 0,
    ensures
        2 * (n / 2) == n,
{
    assert(n == 2 * (n / 2) + (n % 2));
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
    let n = a.len();
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n / 2
        invariant
            n % 2 == 0,
            i <= n / 2,
            res.len() == i,
            forall|k: int|
                0 <= k && k < i as int ==> #[trigger] res@[k] == a[2*k] + a[2*k + 1],
        decreases (n / 2 - i) as int
    {
        proof {
            assert(i + 1 <= n / 2);
            assert(2 * (i + 1) <= 2 * (n / 2));
            assert(n % 2 == 0);
            lemma_even_times_half_equals_self_usize(n);
            assert(2 * (n / 2) == n);
            assert(2 * i + 2 <= n);
            assert(2 * i + 1 < n);
        }
        assert(2 * i + 1 < n);
        let s = a[2 * i] + a[2 * i + 1];
        res.push(s);
        i += 1;
    }
    res
}
// </vc-code>

fn main() {}

}