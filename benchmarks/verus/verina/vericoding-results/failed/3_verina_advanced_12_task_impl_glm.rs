// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed iteration and indexing, changed to exec fn */
exec fn find_first_duplicate_pos(lst: Seq<i32>) -> (pos: Option<(int, int)>)
    ensures
        match pos {
            Some((i, j)) => 0 <= i < j < lst.len() && lst@[i] == lst@[j] &&
                forall|k: int, l: int| 0 <= k < l < lst.len() && lst@[k] == lst@[l] && l <= i ==> k >= i,
            None => forall|i: int, j: int| 0 <= i < j < lst.len() ==> lst@[i] != lst@[j],
        }
{
    if lst.len() < 2 {
        return None;
    }
    let mut found = false;
    let mut first_i = 0;
    let mut first_j = 0;
    let n = lst.len() as usize;

    for i_val in 0..(n-1) {
        let i = i_val as int;
        for j_val in (i_val+1)..n {
            let j = j_val as int;
            if lst@[i] == lst@[j] {
                if !found {
                    found = true;
                    first_i = i;
                    first_j = j;
                }
            }
        }
    }

    if found {
        Some((first_i, first_j))
    } else {
        None
    }
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
    /* code modified by LLM (iteration 5): fixed indexing */
    let pos = find_first_duplicate_pos(*lst);
    match pos {
        Some((i, j)) => lst@[i],
        None => -1,
    }
}
// </vc-code>

}
fn main() {}