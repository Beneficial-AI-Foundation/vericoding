// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(x: i32, lst: Seq<i32>) -> nat {
    lst.filter(|y: i32| y == x).len()
}
// </vc-preamble>

// <vc-helpers>
{
    /* code modified by LLM (iteration 5): brute-force majority search with ghost sequence and invariants relating runtime counts to spec counts */
    let lst_seq = lst@;
    let n = lst_seq.len();
    let n_usize: usize = lst.len();

    let mut i: usize = 0;
    while i < n_usize
        invariant
            i <= n_usize,
            n == lst_seq.len(),
            n_usize == lst.len(),
        decreases n_usize - i
    {
        let candidate: i32 = lst[i];
        let mut j: usize = 0;
        let mut occ: usize = 0;
        while j < n_usize
            invariant
                j <= n_usize,
                occ <= n_usize,
                occ == count_occurrences(candidate, lst_seq[..j]),
                n == lst_seq.len(),
                n_usize == lst.len(),
            decreases n_usize - j
        {
            if lst[j] == candidate {
                occ = occ + 1;
            }
            j = j + 1;
        }

        // At this point occ == count_occurrences(candidate, lst_seq)
        if occ > n_usize / 2 {
            return candidate;
        }
        i = i + 1;
    }

    -1
}

// </vc-helpers>

// <vc-spec>
fn find_majority_element(lst: &Vec<i32>) -> (result: i32)
    ensures ({
        let lst_seq = lst@;
        let n = lst_seq.len();
        let majority = count_occurrences(result, lst_seq) > n / 2 && 
                      forall|x: i32| count_occurrences(x, lst_seq) <= n / 2 || x == result;
        (result == -1 ==> forall|x: i32| count_occurrences(x, lst_seq) <= n / 2) &&
        (result != -1 ==> majority)
    })
// </vc-spec>
// <vc-code>
/* helper modified by LLM (iteration 5): no-op proof helper retained for potential additional lemmas */
proof fn helpers_dummy() { }

// </vc-code>

}
fn main() {}