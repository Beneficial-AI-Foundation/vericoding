use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn remove_duplicates(a: &[i32]) -> (result: Vec<i32>)
    ensures
        forall|x: i32| result@.contains(x) <==> exists|i: int| 0 <= i < a.len() && a[i] == x,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result@[i] != result@[j]
// </vc-spec>
// <vc-code>
{
    let mut res: Vec<i32> = Vec::new();

    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|p: int, q: int| 0 <= p < q < res.len() ==> res@[p] != res@[q],
            forall|x: i32| #[trigger] res@.contains(x) <==> exists|j: int| 0 <= j < i as int && a[j] == x
    {
        let ai = a[i];

        let mut found: bool = false;
        let mut j: usize = 0;
        while j < res.len()
            invariant
                j <= res.len(),
                forall|p: int, q: int| 0 <= p < q < res.len() ==> res@[p] != res@[q],
                found ==> exists|k: int| 0 <= k < j as int && res@[k] == ai,
                forall|k: int| 0 <= k < j as int && res@[k] == ai ==> found
        {
            if res[j] == ai {
                found = true;
            }
            j += 1;
        }

        proof {
            assert(found ==> exists|k: int| 0 <= k < res.len() && res@[k] == ai);
            assert((exists|k: int| 0 <= k < res.len() && res@[k] == ai) ==> found);
            assert(found <==> res@.contains(ai));
        }

        if !found {
            let old_seq = res@;
            res.push(ai);
            proof {
                // Uniqueness after push
                assert(forall|p: int, q: int|
                    0 <= p < q < res.len() ==> res@[p] != res@[q]
                ) by {
                    assert(res.len() == old_seq.len() + 1);
                    assert(res@ == old_seq.push(ai));
                    assert(forall|p: int, q: int|
                        0 <= p < q < old_seq.len() ==> old_seq[p] != old_seq[q]
                    );
                    assert(!old_seq.contains(ai)); // from !found and equivalence above
                    assert(forall|p: int| 0 <= p < old_seq.len() ==> old_seq[p] != ai);
                }

                // Membership equivalence for i+1
                // For any x:
                // - if x == ai, new contains x and exists j < i+1 (j == i)
                // - if x != ai, new contains x iff old contains x, which by invariant
                //   holds iff exists j < i with a[j] == x; since x != ai, the existence
                //   over [0, i] is same as over [0, i+1)
                assert(forall|x: i32|
                    #[trigger] res@.contains(x) <==> exists|j: int| 0 <= j < (i as int + 1) && a[j] == x
                ) by {
                    assert(res@ == old_seq.push(ai));
                    assert(!old_seq.contains(ai));
                    assert(forall|x: i32|
                        x != ai ==> ((old_seq.push(ai)).contains(x) <==> old_seq.contains(x))
                    );
                    assert((old_seq.push(ai)).contains(ai));
                    assert(forall|x: i32|
                        #[trigger] old_seq.contains(x) <==> exists|j: int| 0 <= j < i as int && a[j] == x
                    );
                    assert(exists|j: int| 0 <= j < i as int + 1 && a[j] == ai) by {
                        assert(0 <= i as int && i as int < i as int + 1);
                        assert(a[i as int] == ai);
                    }
                    assert(forall|x: i32|
                        x != ai ==> (
                            (exists|j: int| 0 <= j < i as int && a[j] == x)
                            <==>
                            (exists|j: int| 0 <= j < i as int + 1 && a[j] == x)
                        )
                    ) by {
                        // Adding the index i doesn't add a witness for x != ai
                        assert(a[i as int] == ai);
                    }
                }
            }
        } else {
            // res unchanged
            proof {
                // Uniqueness unchanged
                assert(forall|p: int, q: int| 0 <= p < q < res.len() ==> res@[p] != res@[q]);

                // Membership equivalence for i+1 when res unchanged
                assert(forall|x: i32|
                    #[trigger] res@.contains(x) <==> exists|j: int| 0 <= j < (i as int + 1) && a[j] == x
                ) by {
                    assert(forall|x: i32|
                        #[trigger] res@.contains(x) <==> exists|j: int| 0 <= j < i as int && a[j] == x
                    );
                    assert(forall|x: i32|
                        (exists|j: int| 0 <= j < i as int && a[j] == x) ==> (exists|j: int| 0 <= j < i as int + 1 && a[j] == x)
                    );
                    // For the reverse direction, if there exists j < i+1 with a[j]==x,
                    // then either j < i or j == i. If j == i, then x == ai, which must
                    // already be in res (since found), so there also exists j' < i.
                    assert(forall|x: i32|
                        (exists|j: int| 0 <= j < i as int + 1 && a[j] == x) ==> res@.contains(x)
                    ) by {
                        if exists|j: int| 0 <= j < i as int && a[j] == x {
                            assert(res@.contains(x));
                        } else {
                            // then the only possible witness is j == i, hence x == ai
                            assert(a[i as int] == ai);
                            assert(x == ai);
                            assert(res@.contains(ai)); // since found
                        }
                    }
                }
            }
        }

        i += 1;
    }

    res
}
// </vc-code>

fn main() {
}

}