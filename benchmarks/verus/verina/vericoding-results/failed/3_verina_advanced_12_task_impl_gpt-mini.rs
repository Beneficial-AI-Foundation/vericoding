// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): runtime helper using Vec to avoid ghost nat types */
fn find_prev_index_run(lst: &Seq<i32>, j: usize) -> Option<usize>
{
    let v = lst.to_vec();
    let mut k: usize = 0;
    while k < j
        invariant
            k <= j,
        decreases j - k
    {
        if v[k] == v[j] {
            return Some(k);
        }
        k = k + 1;
    }
    None
}
// </vc-helpers>

// <vc-spec>
fn first_duplicate(lst: &Seq<i32>) -> (result: i32)
    ensures

        (result == -1 ==> forall|i: int, j: int| 0 <= i < j < lst.len() ==> lst[i] != lst[j]) &&

        (result != -1 ==> 
            exists|i: int, j: int| 0 <= i < j < lst.len() && lst[i] == lst[j] && lst[i] == result &&
            forall|k: int, l: int| 0 <= k < l < lst.len() && lst[k] == lst[l] && l <= i ==> k >= i
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): scan sequence using Vec to find earliest duplicate pair and return its value or -1 */
    let v = lst.to_vec();
    let n: usize = v.len();
    let mut best_j: Option<usize> = None;
    let mut best_i: usize = 0;
    let mut j: usize = 0;
    while j < n
        invariant
            j <= n,
        decreases n - j
    {
        let prev = find_prev_index_run(lst, j);
        if let Some(p) = prev {
            match best_j {
                None => {
                    best_j = Some(j);
                    best_i = p;
                }
                Some(bj) => {
                    if j < bj {
                        best_j = Some(j);
                        best_i = p;
                    }
                }
            }
        }
        j = j + 1;
    }
    match best_j {
        None => -1,
        Some(_) => v[best_i],
    }
}
// </vc-code>

}
fn main() {}