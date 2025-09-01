use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn adj_to_all_recursive(lst: &[i32], n: int, i: int, j: int)
    requires
        0 <= i && i < j && j < n,
        forall|m: int| 0 <= m && m + 1 < n ==> lst[m] <= lst[m + 1],
    decreases j - i
    ensures
        lst[i] <= lst[j]
{
    if j == i + 1 {
        // direct from adjacent assumption
        assert(lst[i] <= lst[j]);
    } else {
        adj_to_all_recursive(lst, n, i, j - 1);
        // from adjacent assumption for j-1
        assert(lst[j - 1] <= lst[j]);
        // transitivity
        assert(lst[i] <= lst[j]);
    }
}

proof fn adjacent_to_all(lst: &[i32], n: int)
    requires
        n >= 1,
        n as usize <= lst.len(),
        forall|m: int| 0 <= m && m + 1 < n ==> lst[m] <= lst[m + 1],
    ensures
        forall|i: int, j: int| 0 <= i && i < j && j < n ==> lst[i] <= lst[j]
{
    assert(forall|i: int, j: int| 0 <= i && i < j && j < n ==>
        {
            adj_to_all_recursive(lst, n, i, j);
            lst[i] <= lst[j]
        }
    );
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
    // impl-start
    let n: int = lst.len() as int;
    let mut k: int = 0;

    while k + 1 < n
        invariant 0 <= k && k <= n - 1
        invariant forall|m: int| 0 <= m && m + 1 <= k ==> lst[m] <= lst[m + 1]
        decreases n - k
    {
        let a: i32 = lst[k as usize];
        let b: i32 = lst[(k + 1) as usize];

        if a > b {
            proof {
                // relate runtime values to specification indexing
                assert(a == lst[k as usize]);
                assert(b == lst[(k + 1) as usize]);
                assert(a > b);
                // witness the violating pair
                assert(exists|i: int, j: int| i == k && j == k + 1 && 0 <= i && i < j && j < n && lst[i] > lst[j]);
            }
            return false;
        } else {
            proof {
                // need to show the invariant holds for k+1
                assert(forall|m: int| 0 <= m && m + 1 <= k + 1 ==>
                    {
                        if m + 1 <= k {
                            // previous invariant covers this case
                            assert(lst[m] <= lst[m + 1]);
                            lst[m] <= lst[m + 1]
                        } else {
                            // m + 1 == k + 1 -> m == k
                            assert(m + 1 == k + 1);
                            assert(m == k);
                            assert(a == lst[k as usize]);
                            assert(b == lst[(k + 1) as usize]);
                            assert(a <= b);
                            assert(lst[m] <= lst[m + 1]);
                            lst[m] <= lst[m + 1]
                        }
                    }
                );
            }
            k = k + 1;
        }
    }

    proof {
        // From the loop invariant at termination we have all adjacent pairs non-decreasing.
        // Prove k == n - 1 at loop exit.
        assert(!(k + 1 < n));
        assert(0 <= k && k <= n - 1);
        assert(k + 1 >= n);
        assert(k >= n - 1);
        assert(k == n - 1);

        // Now lift adjacent property to all i < j < n using helper.
        assert(forall|m: int| 0 <= m && m + 1 < n ==>
            {
                // from k == n-1 we get m+1 <= k
                assert(m + 1 <= k);
                assert(lst[m] <= lst[m + 1]);
                lst[m] <= lst[m + 1]
            }
        );

        adjacent_to_all(lst, n);
    }

    true
    // impl-end
}
// </vc-code>

fn main() {}
}