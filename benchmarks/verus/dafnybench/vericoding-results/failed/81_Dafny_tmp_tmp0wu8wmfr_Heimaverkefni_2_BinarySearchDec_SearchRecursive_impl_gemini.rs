// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no change needed, just updating comment */
proof fn lemma_sorted_ge(a: Seq<int>, x: int, i: int, m: int, j: int)
    requires
        i <= m < j,
        a[m] >= x,
        forall|p: int, q: int| i <= p < q < j ==> a[p] >= a[q],
    ensures
        forall|r: int| i <= r <= m ==> a[r] >= x,
{
    assert forall|r: int| i <= r <= m implies a[r] >= x by {
        if r < m {
            assert(a[r] >= a[m]);
        }
    };
}

/* helper modified by LLM (iteration 5): no change needed, just updating comment */
proof fn lemma_sorted_lt(a: Seq<int>, x: int, i: int, m: int, j: int)
    requires
        i <= m < j,
        a[m] < x,
        forall|p: int, q: int| i <= p < q < j ==> a[p] >= a[q],
    ensures
        forall|r: int| m <= r < j ==> a[r] < x,
{
    assert forall|r: int| m <= r < j implies a[r] < x by {
        if r > m {
            assert(a[m] >= a[r]);
        }
    };
}
// </vc-helpers>

// <vc-spec>
fn search_recursive(a: Seq<int>, i: int, j: int, x: int) -> (k: int)
    requires 
        0 <= i <= j <= a.len(),
        forall|p: int, q: int| i <= p < q < j ==> a[p] >= a[q],
    ensures 
        i <= k <= j,
        forall|r: int| i <= r < k ==> a[r] >= x,
        forall|r: int| k <= r < j ==> a[r] < x,
    decreases j - i
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed illegal cast for sequence indexing */
    if i == j {
        i
    } else {
        let m: int = i + (j - i) / 2;
        
        if a[m] >= x {
            lemma_sorted_ge(a, x, i, m, j);
            let k = search_recursive(a, m + 1, j, x);
            
            assert forall|r: int| i <= r < k implies a[r] >= x by {
                if r <= m {
                    // lemma_sorted_ge ensures this
                } else {
                    // recursive call ensures this
                }
            };
            k
        } else {
            lemma_sorted_lt(a, x, i, m, j);
            let k = search_recursive(a, i, m, x);

            assert forall|r: int| k <= r < j implies a[r] < x by {
                if r < m {
                    // recursive call ensures this
                } else {
                    // lemma_sorted_lt ensures this
                }
            };
            k
        }
    }
}
// </vc-code>

}
fn main() {}