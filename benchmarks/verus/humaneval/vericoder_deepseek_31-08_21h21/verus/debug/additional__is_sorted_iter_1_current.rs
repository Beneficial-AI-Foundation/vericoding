use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_sorted_property(s: Seq<i32>, i: int, j: int)
    requires
        0 <= i && i < j && j < s.len(),
        forall|k: int, l: int| 0 <= k && k < l && l < s.len() ==> s[k] <= s[l],
    ensures
        s[i] <= s[j],
{
}

proof fn lemma_not_sorted_exists_first_violation(s: Seq<i32>)
    requires
        !(forall|i: int, j: int| 0 <= i && i < j && j < s.len() ==> s[i] <= s[j]),
        s.len() >= 1,
    ensures
        exists|i: int| 1 <= i && i < s.len() && s[i-1] > s[i],
{
}

proof fn lemma_not_sorted_from_first_violation(s: Seq<i32>, i: int)
    requires
        1 <= i && i < s.len(),
        s[i-1] > s[i],
    ensures
        !(forall|k: int, l: int| 0 <= k && k < l && l < s.len() ==> s[k] <= s[l]),
        exists|k: int, l: int| 0 <= k && k < l && l < s.len() && s[k] > s[l],
{
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
    let mut idx = 0;
    let n = lst.len();
    while idx < n - 1
        invariant
            0 <= idx <= n - 1,
            forall|i: int, j: int| 0 <= i && i < j && j <= idx ==> lst[i] <= lst[j],
        decreases n - 1 - idx,
    {
        if lst[idx] > lst[idx + 1] {
            proof {
                lemma_not_sorted_from_first_violation(lst@, idx as int + 1);
            }
            return false;
        }
        idx = idx + 1;
        proof {
            if idx > 0 {
                assert forall|i: int, j: int| 0 <= i && i < j && j <= idx implies lst[i] <= lst[j] by {
                    if j == idx {
                        lemma_sorted_property(lst@, i, idx as int - 1);
                        assert(lst[i] <= lst[idx as int - 1]);
                        assert(lst[idx as int - 1] <= lst[idx as int]);
                    } else {
                        assert(j < idx);
                    }
                };
            }
        }
    }
    proof {
        assert forall|i: int, j: int| 0 <= i && i < j && j < n implies lst[i] <= lst[j] by {
            if j < n - 1 {
                assert(j <= idx);
            } else if j == n - 1 {
                if i < n - 2 {
                    lemma_sorted_property(lst@, i, (n - 2) as int);
                    assert(lst[i] <= lst[(n - 2) as int]);
                }
                assert(lst[(n - 2) as int] <= lst[(n - 1) as int]);
            }
        };
    }
    true
}
// </vc-code>

fn main() {}
}