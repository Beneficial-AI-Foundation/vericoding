// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove reverse index is within range */
fn rev_index_in_range(n: int, i: int)
    requires
        0 <= i && i < n,
    ensures
        0 <= n - 1 - i && n - 1 - i < n,
{
    proof {
        // i < n implies i <= n - 1, so n - 1 - i >= 0
        assert(n - 1 - i >= 0);
        // i >= 0 implies n - 1 - i < n
        assert(n - 1 - i < n);
    }
}

// </vc-helpers>

// <vc-spec>
fn is_palindrome(x: Seq<char>) -> (result: bool)
    ensures
        result <==> (forall|i: int| 0 <= i < x.len() ==> #[trigger] x[i] == x[x.len() - 1 - i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement palindrome check with proper proof using loop */
    let n = x.len();
    let mut l: int = 0;
    let mut r: int = n - 1;
    while l < r
        invariant
            0 <= l <= n,
            -1 <= r && r < n,
            r == n - l - 1,
            forall|i: int| 0 <= i < l ==> x@[i] == x@[n - 1 - i],
        decreases r - l
    {
        if x@[l] != x@[r] {
            return false;
        }
        l = l + 1;
        r = r - 1;
    }
    proof {
        assert(forall|i: int| 0 <= i < n ==> x@[i] == x@[n - 1 - i]) by {
            if !(0 <= i && i < n) {
                // antecedent false, implication holds vacuously
                assert((0 <= i && i < n) ==> x@[i] == x@[n - 1 - i]);
            } else {
                if i < l {
                    // already proven by the loop invariant
                    assert(x@[i] == x@[n - 1 - i]);
                } else if i > r {
                    let j = n - 1 - i;
                    // use helper to get j in range
                    rev_index_in_range(n, i);
                    // derive l == n - r - 1 from invariant r == n - l - 1
                    assert(l == n - r - 1);
                    // from i > r we get n - 1 - i < n - 1 - r
                    assert(n - 1 - i < n - 1 - r);
                    // compute n - 1 - r equals l
                    assert(n - 1 - r == l);
                    // hence j < l
                    assert(j < l);
                    // j is within range
                    assert(0 <= j && j < n);
                    assert(x@[j] == x@[n - 1 - j]);
                    assert(n - 1 - j == i);
                    assert(x@[i] == x@[n - 1 - i]);
                } else {
                    // l <= i <= r
                    assert(l <= i && i <= r);
                    // loop exit implies not (l < r)
                    assert(!(l < r));
                    assert(l >= r);
                    // from l <= r (from i bounds) and l >= r get equality
                    assert(l <= r);
                    assert(l == r);
                    assert(i == l);
                    assert(i == r);
                    assert(i == n - 1 - i);
                    assert(x@[i] == x@[n - 1 - i]);
                }
            }
        };
    }
    true
}

// </vc-code>

}
fn main() {}