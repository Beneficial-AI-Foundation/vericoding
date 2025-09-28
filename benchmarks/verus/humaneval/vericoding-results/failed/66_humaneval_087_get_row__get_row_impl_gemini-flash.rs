// <vc-preamble>
use vstd::prelude::*;

verus! {

type SortSeqState = Seq<(int, int)>;

spec fn less(a: (int, int), b: (int, int)) -> bool {
    let (x, y) = a;
    let (u, v) = b;
    x < u || (x == u && y > v)
}

spec fn less_eq(a: (int, int), b: (int, int)) -> bool {
    let (x, y) = a;
    let (u, v) = b;
    (x == u && y == v) || less(a, b)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The helper function `lemma_insert_sorted` is used to prove that inserting an element into a sorted sequence maintains the sorted property. The `lemma_compare_pairs` is a transitive property for `less_eq` which is crucial when reasoning about elements in different segments of the sequence after insertion. The structure of the proof in `lemma_insert_sorted` is sound, as it leverages the already established sorted portions and the `less_eq` relation with the inserted element to show that the entire new sequence remains sorted. No changes are needed as the issue is not within the helper, but the calling context. */
verus!
{
    proof fn lemma_compare_pairs(p1: (int, int), p2: (int, int), p3: (int, int))
        requires less_eq(p1, p2),
                 less_eq(p2, p3),
        ensures less_eq(p1, p3),
    {
        // if p1 < p2 then if p2 < p3 then p1 < p3
        // if p1 == p2 then if p2 < p3 then p1 < p3
        // if p1 == p2 then if p2 == p3 then p1 == p3
    }

    proof fn lemma_insert_sorted(s: Seq<(int, int)>, p: (int, int), i: int)
        requires
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> less_eq(s[j], p),
            forall|j: int| i <= j < s.len() ==> less_eq(p, s[j]),
            forall|j: int, k: int| 0 <= j < k < s.len() ==> less_eq(s[j], s[k]),
        ensures
            forall|j: int, k: int| 0 <= j < k < s.insert(i, p).len() ==> less_eq(s.insert(i, p)[j], s.insert(i, p)[k]),
    {
        // Proof that the new sequence remains sorted
        assert forall|j: int, k: int| 0 <= j < k < s.insert(i, p).len() implies less_eq(s.insert(i, p)[j], s.insert(i, p)[k]) by {
            let new_s = s.insert(i, p);
            if j < i && k < i {
                assert(less_eq(new_s[j], new_s[k]));
            } else if j < i && k == i {
                assert(less_eq(new_s[j], new_s[k]));
            } else if j < i && k > i {
                lemma_compare_pairs(new_s[j], new_s[i], new_s[k]);
                assert(less_eq(new_s[j], new_s[k]));
            } else if j == i && k > i {
                assert(less_eq(new_s[j], new_s[k]));
            } else if j > i && k > i {
                assert(less_eq(new_s[j], new_s[k]));
            } else if j == i && k == i {
                // This case is not possible since j < k
                unreachable!();
            } else if j > i && k == i {
                // This case is not possible since j < k
                unreachable!();
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn get_row(lst: &Vec<Vec<i8>>, x: i8) -> (pos: SortSeqState)
    ensures 
        (forall|i: int| 0 <= i < pos.len() ==> #[trigger] pos[i].0 >= 0 && #[trigger] pos[i].1 >= 0 && {
            let (a, b) = pos[i];
            0 <= a < lst@.len() && 0 <= b < lst@[a].len() && lst@[a][b] as int == x as int
        }) &&
        (forall|i: int, j: int| 0 <= i < lst@.len() && 0 <= j < lst@[i].len() && lst@[i][j] as int == x as int ==> #[trigger] pos.contains((i, j))) &&
        (forall|i: int, j: int| 0 <= i < j < pos.len() ==> #[trigger] less_eq(pos[i], pos[j]))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed a compilation error regarding `lst.len()` in an invariant, which was missing `,` after `lst.len()` in the range assertion. Also, adjusted the loop invariant for the inner loop to correctly reflect the current state of `result_seq` when a new element `(i, j)` is being considered for insertion. Removed incorrect assertions related to `j as int` and `lst[i].len()` in the inner loop's invariant, as they were not directly contributing to proving `result_seq`'s properties and causing issues. The main logic of iterating through the nested lists and inserting elements in a sorted manner into `result_seq` remains consistent. */
{
    let mut result_seq: SortSeqState = Seq::empty();

    let mut i: usize = 0;
    while (i as int) < lst.len()
        invariant
            0 <= i as int && i as int <= lst.len(),
            forall|r: int, c: int| 0 <= r < i as int && 0 <= c < lst@[r].len() && lst@[r][c] == x
                ==> result_seq.contains((r, c)),
            forall|idx: int| 0 <= idx < result_seq.len() ==> #[trigger] result_seq[idx].0 >= 0 && #[trigger] result_seq[idx].1 >= 0 && {
                let (a, b) = result_seq[idx];
                0 <= a < i as int && 0 <= b < lst@[a].len() && lst@[a][b] == x
            },
            forall|idx: int, jdx: int| 0 <= idx < jdx < result_seq.len() ==> less_eq(result_seq[idx], result_seq[jdx]),
    {
        let mut j: usize = 0;
        while (j as int) < lst[i].len()
            invariant
                0 <= i as int < lst.len(),
                0 <= j as int && j as int <= lst[i].len(),
                forall|r: int, c: int| 0 <= r < i as int && 0 <= c < lst@[r].len() && lst@[r][c] == x
                    ==> result_seq.contains((r, c)),
                forall|c: int| 0 <= c < j as int && lst@[i as int][c] == x ==> result_seq.contains((i as int, c)),
                forall|idx: int| 0 <= idx < result_seq.len() ==> #[trigger] result_seq[idx].0 >= 0 && #[trigger] result_seq[idx].1 >= 0 && {
                    let (a, b) = result_seq[idx];
                    // The elements in result_seq are from rows < i, or row i and column < j.
                    0 <= a < lst@.len() && 0 <= b < lst@[a].len() && lst@[a][b] == x
                    && (a < i as int || (a == i as int && b < j as int))
                },
                forall|idx: int, jdx: int| 0 <= idx < jdx < result_seq.len() ==> less_eq(result_seq[idx], result_seq[jdx]),
        {
            if lst[i][j] == x {
                let p = (i as int, j as int);
                let mut insert_idx: int = 0;
                while insert_idx < result_seq.len() as int
                    invariant
                        0 <= insert_idx && insert_idx <= result_seq.len() as int,
                        forall|k: int| 0 <= k < insert_idx ==> less_eq(result_seq[k], p),
                        forall|k: int, l: int| 0 <= k < l < result_seq.len() ==> less_eq(result_seq[k], result_seq[l]),

                        // The outer loop invariants just need to hold for the current state
                        0 <= i as int < lst.len(),
                        0 <= j as int < lst[i].len(),
                        forall|r: int, c: int| 0 <= r < i as int && 0 <= c < lst@[r].len() && lst@[r][c] == x
                            ==> result_seq.contains((r, c)),
                        forall|c: int| 0 <= c < j as int && lst@[i as int][c] == x
                            ==> result_seq.contains((i as int, c)),
                        forall|idx: int| 0 <= idx < result_seq.len() ==> #[trigger] result_seq[idx].0 >= 0 && #[trigger] result_seq[idx].1 >= 0 && {
                            let (a, b) = result_seq[idx];
                            0 <= a < lst@.len() && 0 <= b < lst@[a].len() && lst@[a][b] == x
                            && (a < i as int || (a == i as int && b < j as int))
                        },
                {
                    if less(p, result_seq@[insert_idx]) {
                        break;
                    }
                    insert_idx = insert_idx + 1;
                }
                proof {
                    lemma_insert_sorted(result_seq, p, insert_idx);
                }
                result_seq = result_seq.insert(insert_idx, p);
            }
            j = j + 1;
        }
        i = i + 1;
    }

    result_seq
}
// </vc-code>


}

fn main() {}