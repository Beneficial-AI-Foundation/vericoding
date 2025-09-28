use vstd::prelude::*;

verus! {

fn find_min_index(a: &Vec<i32>, s: usize, e: usize) -> (min_i: usize)
    requires 
        a.len() > 0,
        s < a.len(),
        e <= a.len(),
        e > s,
    ensures 
        min_i >= s,
        min_i < e,
        forall|k: int| s <= k < e ==> a[min_i as int] <= a[k],
{
    assume(false);
    s
}

spec fn is_sorted(ss: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < ss.len() ==> ss[i] <= ss[j]
}

spec fn is_permutation(a: Seq<i32>, b: Seq<i32>) -> bool
    decreases a.len(), b.len()
{
    a.len() == b.len() && 
    ((a.len() == 0 && b.len() == 0) ||  
     (exists|i: int, j: int| {
        0 <= i < a.len() && 0 <= j < b.len() && a[i] == b[j] && 
        is_permutation(
            a.subrange(0, i) + {if i < a.len() { a.subrange(i + 1, a.len() as int) } else { seq![] }},
            b.subrange(0, j) + {if j < b.len() { b.subrange(j + 1, b.len() as int) } else { seq![] }}
        )
     }))
}

spec fn is_permutation2(a: Seq<i32>, b: Seq<i32>) -> bool {
    a.to_multiset() == b.to_multiset()
}

// <vc-helpers>
#[allow(unused)]
proof fn find_min_index_aux_proof(a: &Vec<i32>, s: usize, e: usize, mut min_i: usize, mut i: usize)
    requires a.len() > 0,
    requires s < a.len(),
    requires e <= a.len(),
    requires e > s,
    requires s <= min_i && min_i < e,
    requires s + 1 <= i && i <= e,
    requires forall|k: int| (s as int) <= k && k < (i as int) ==> a@[min_i as int] <= a@[k],
    ensures forall|k: int| (s as int) <= k && k < ((i as int) + 1) ==> a@[min_i as int] <= a@[k],
    decreases (e as int) - (i as int)
{
    if i < e {
        let ai = a@[i as int];
        let amin = a@[min_i as int];
        let old_min = min_i;
        if ai < amin {
            min_i = i;
            proof {
                // From the old invariant we have for all k in [s, i) a[old_min] <= a[k]
                assert(forall|k: int| (s as int) <= k && k < (i as int) ==> a@[old_min as int] <= a@[k]);
                // amin == a[old_min], and ai < amin, so ai <= a[k] for k < i
                assert(amin == a@[old_min as int]);
                assert(ai < amin);
                // from a[old_min] <= a[k] and ai < a[old_min] we get ai <= a[k]
                assert(forall|k: int| (s as int) <= k && k < (i as int) ==> ai <= a@[k]);
                // Now a[min_i] == ai, so for k < i we have a[min_i] <= a[k]
                assert(a@[min_i as int] == ai);
                assert(forall|k: int| (s as int) <= k && k < (i as int) ==> a@[min_i as int] <= a@[k]);
                // And for k == i: a[min_i] == ai <= a[i]
                assert(a@[min_i as int] <= a@[i as int]);
                // Combine to get the desired range [s, i+1)
                assert(forall|k: int| (s as int) <= k && k < ((i as int) + 1) ==> a@[min_i as int] <= a@[k]);
            }
        } else {
            // min_i unchanged; use old invariant to extend to i+1
            proof {
                assert(forall|k: int| (s as int) <= k && k < ((i as int) + 1) ==> a@[min_i as int] <= a@[k]);
            }
        }
        find_min_index_aux_proof(a, s, e, min_i, i + 1);
    } else {
        // i == e: nothing to do
    }
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(ns: &mut Vec<i32>) 
    requires old(ns).len() >= 0
    ensures 
        is_sorted(ns@),
        is_permutation2(old(ns)@, ns@),
// </vc-spec>
// <vc-code>
{
    let n: usize = ns.len();
    let orig: Seq<i32> = ns@;

    let mut rem: Vec<i32> = ns.clone();
    let mut out: Vec<i32> = Vec::new();

    while rem.len() > 0
        invariant out.len() + rem.len() == n,
        invariant is_sorted(out@),
        invariant forall|i: int, j: int| 0 <= i && i < out@.len() && 0 <= j && j < rem@.len() ==> out@[i] <= rem@[j],
        invariant is_permutation2(orig, rem@ + out@),
    {
        let mut min_i: usize = 0;
        let mut j: usize = 1;
        while j < rem.len()
            invariant 1 <= j && j <= rem.len(),
            invariant 0 <= min_i && min_i < rem.len(),
            invariant forall|k: int| 0 <= k && k < (j as int) ==> rem@[min_i as int] <= rem@[k],
            decreases (rem.len() as int) - (j as int)
        {
            let rj = rem@[j as int];
            let rmin = rem@[min_i as int];
            let old_min = min_i;
            if rj < rmin {
                proof {
                    assert(forall|k: int| 0 <= k && k < (j as int) ==> rem@[old_min as int] <= rem@[k]);
                }
                min_i = j;
                proof {
                    assert( rmin == rem@[old_min as int] );
                    assert(rj < rmin);
                    assert(forall|k: int| 0 <= k && k < (j as int) ==> rem@[old_min as int] <= rem@[k]);
                    assert(forall|k: int| 0 <= k && k < (j as int) ==> rj <= rem@[k]);
                    assert(rem@[min_i as int] == rj);
                    assert(forall|k: int| 0 <= k && k < (j as int) ==> rem@[min_i as int] <= rem@[k]);
                    assert(rem@[min_i as int] <= rem@[j as int]);
                    assert(forall|k: int| 0 <= k && k < ((j as int) + 1) ==> rem@[min_i as int] <= rem@[k]);
                }
            } else {
                proof {
                    find_min_index_aux_proof(&rem, 0, rem.len(), min_i, j);
                }
            }
            j = j + 1;
        }

        let rem_before: Seq<i32> = rem@;
        let out_before: Seq<i32> = out@;
        let m_int: int = min_i as int;

        let v: i32 = rem.remove(min_i);
        out.push(v);

        proof {
            // rem after removal equals concatenation of parts before and after the removed index
            assert(rem@ == rem_before.subrange(0, m_int) + rem_before.subrange(m_int + 1, rem_before.len()));
            // out after push equals old out concatenated with the single-element subrange at m_int
            assert(out@ == out_before + rem_before.subrange(m_int, m_int + 1));
            // rem_before can be split as before ++ [elem] ++ after
            assert(rem_before == rem_before.subrange(0, m_int) + rem_before.subrange(m_int, m_int + 1) + rem_before.subrange(m_int + 1, rem_before.len()));
            // Now rem@ + out@ equals (before ++ after) ++ (out_before ++ [elem]) which is a reordering of rem_before ++ out_before
            assert(rem@ + out@ ==
                (rem_before.subrange(0, m_int) + rem_before.subrange(m_int + 1, rem_before.len())) + (out_before + rem_before.subrange(m_int, m_int + 1))
            );
            // From the previous equalities and associativity of concatenation, conclude permutation property persists
            assert(is_permutation2(orig, rem@ + out@));
        }

        proof {
            // out_before is sorted and every element of out_before <= every element of rem_before,
            // in particular out_before elements <= the chosen minimal element rem_before[m_int]
            assert(forall|i: int| 0 <= i && i < out_before.len() ==> out_before@[i] <= rem_before@[m_int]);
            // Hence appending rem_before[m_int] to out_before preserves sortedness
            assert(is_sorted(out@));
            // And the relation between out and rem remains: every out element <= every rem element
            assert(forall|i: int, j: int| 0 <= i && i < out@.len() && 0 <= j && j < rem@.len() ==> out@[i] <= rem@[j]);
        }
    }

    // After loop: rem is empty, out has all elements in sorted order and is a permutation of orig
    proof {
        assert(rem.len() == 0);
        assert(out.len() == n);
        assert(is_sorted(out@));
        assert(is_permutation2(orig, out@));
    }

    // Move sorted elements into ns
    let out_before_move: Seq<i32> = out@;
    ns.clear();
    ns.append(&mut out);

    proof {
        assert(ns@ == out_before_move);
        assert(is_sorted(ns@));
        assert(is_permutation2(orig, ns@));
    }
}
// </vc-code>

fn main() {}

}