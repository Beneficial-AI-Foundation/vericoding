use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_sum_of_naturals(n: nat)
    ensures
        2 * (n * (n + 1)) / 2 == n * (n + 1),
{
    assert(n * (n + 1) == n * (n + 1));
}

proof fn lemma_formula_within_usize(n: nat)
    requires
        n <= (usize::MAX as nat) / 2 + 1,
    ensures
        (n * (n + 1)) / 2 <= usize::MAX as nat,
{
    if n <= 1 {
        assert((n * (n + 1)) / 2 <= 1);
    } else {
        let k = n / 2;
        let m = n - k;
        assert(n == k + m);
        assert(k * m <= (n * n) / 4);
        assert((n * (n + 1)) / 2 <= (n * (n + 1)) / 2);
        assert((n * (n + 1)) / 2 <= (n * n + n) / 2);
        assert((n * n + n) / 2 <= (n * n + n * n) / 2);
        assert((n * n + n * n) / 2 == n * n);
        assert(n * n <= ((usize::MAX as nat) / 2 + 1) * ((usize::MAX as nat) / 2 + 1));
        assert(((usize::MAX as nat) / 2 + 1) * ((usize::MAX as nat) / 2 + 1) <= (usize::MAX as nat) * (usize::MAX as nat) / 4 + (usize::MAX as nat) + 1);
        assert((usize::MAX as nat) * (usize::MAX as nat) / 4 + (usize::MAX as nat) + 1 <= usize::MAX as nat * 2);
        assert(usize::MAX as nat * 2 / 2 == usize::MAX as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn count_non_empty_substrings(s: Seq<char>) -> (count: usize)
    ensures 
        count >= 0,
        count == (s.len() * (s.len() + 1)) / 2, // Formula for the number of non-empty substrings of a string
// </vc-spec>
// <vc-code>
{
    let n = s.len();
    lemma_sum_of_naturals(n);
    lemma_formula_within_usize(n);
    let total = (n * (n + 1)) / 2;
    total as usize
}
// </vc-code>

fn main() {
}

}