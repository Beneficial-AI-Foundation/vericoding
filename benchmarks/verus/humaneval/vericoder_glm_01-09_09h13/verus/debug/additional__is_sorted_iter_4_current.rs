use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_by_gap(lst: &[i32], g: nat)
    requires
        g >= 1,
        forall|i: int| 0 <= i < lst.len() - 1 ==> lst[i] <= lst[i+1],
    ensures
        forall|i: int| 0 <= i && i + g < lst.len() ==> lst[i] <= lst[i + g]
    decreases g
{
    if g == 1 {
        assert forall|i: int| 0<=i && i+1 < lst.len() implies lst[i] <= lst[i+1] by {
            // Directly from the requires condition
        }
    } else {
        lemma_by_gap(lst, (g - 1) as nat);
        assert forall|i: int| 0<=i && i+g < lst.len() implies lst[i] <= lst[i+g] by {
            // Since g >= 2, we have i+1 < lst.len() because i+g < lst.len()
            // By adjacent condition: lst[i] <= lst[i+1]
            // By induction hypothesis: lst[i+1] <= lst[i+g]
            // By transitivity: lst[i] <= lst[i+g]
            let next_index = i + 1;
            assert(lst[i] <= lst[next_index]); // adjacent condition
            assert(next_index + (g - 1) == i + g); // arithmetic
            lemma_by_gap(lst, (g - 1) as nat); // applies to next_index with gap g-1
            assert(lst[next_index] <= lst[next_index + (g - 1)]); // by induction
            assert(lst[i] <= lst[i + g]); // by transitivity
        }
    }
}

proof fn adjacent_implies_sorted(lst: &[i32])
    requires
        forall|i: int| 0 <= i < lst.len() - 1 ==> lst[i] <= lst[i+1],
    ensures
        forall|i: int, j: int| 0 <= i && i < j && j < lst.len() ==> lst[i] <= lst[j]
{
    let n = lst.len();
    assert forall|i: int, j: int| 0 <= i && i < j && j < n implies lst[i] <= lst[j] by {
        let g = j - i;
        lemma_by_gap(lst, g as nat);
        assert(i + g == j); // by definition
        assert(lst[i] <= lst[i + g]); // from lemma_by_gap
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn is_sorted(lst: &[i32]) -> (result: bool)
    // pre-conditions-start
    requires
        lst.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result <== forall|i: int, j: int| 0 <= i && i < j && j < lst.len() ==> lst[i] <= lst[j],
        !result ==> exists|i: int, j: int| 0 <= i && i < j && j < lst.len() && lst[i] > lst[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = lst.len();
    let mut i = 0;
    while i < n - 1
        invariant
            0 <= i <= n - 1,
            forall|k: int| 0 <= k < i ==> lst[k] <= lst[k+1],
    {
        if lst[i] > lst[i+1] {
            return false;
        }
        i = i + 1;
    }
    proof {
        adjacent_implies_sorted(lst);
    }
    true
}
// </vc-code>

fn main() {}
}