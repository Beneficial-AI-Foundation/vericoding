// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn seq_min(s: Seq<int>) -> int 
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.len() == 1 {
        s[0]
    } else {
        let tail_min = seq_min(s.subrange(1, s.len() as int));
        if s[0] <= tail_min {
            s[0]
        } else {
            tail_min
        }
    }
}

spec fn valid_input(arr: Seq<int>) -> bool {
    arr.len() >= 2 && 
    exists|i: int, j: int| 0 <= i < j < arr.len() && #[trigger] arr[i] == #[trigger] arr[j] && arr[i] == seq_min(arr)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No change. */
spec fn arr_to_seq(arr: Vec<i8>) -> Seq<int> {
    arr@.map(|_i, v| v as int)
}
// </vc-helpers>

// <vc-spec>
fn solve(arr: Vec<i8>) -> (result: u8)
    requires 
        valid_input(arr_to_seq(arr)),
    ensures 
        result > 0,
        result as int <= arr.len() - 1,
        exists|i: int, j: int| 0 <= i < j < arr.len() && #[trigger] arr_to_seq(arr)[i] == #[trigger] arr_to_seq(arr)[j] && arr_to_seq(arr)[i] == seq_min(arr_to_seq(arr)) && j - i == result as int,
        forall|i: int, j: int| 0 <= i < j < arr.len() && #[trigger] arr_to_seq(arr)[i] == #[trigger] arr_to_seq(arr)[j] && arr_to_seq(arr)[i] == seq_min(arr_to_seq(arr)) ==> j - i >= result as int,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed loop variables `i` and `j` to `usize` to match `s.len()` type and resolve '`nat` and `int` can only be used in ghost code' errors. Casted `min_diff` to `usize` for invariant checks. */
{
    let s = arr_to_seq(arr);
    let min_val = seq_min(s);

    let mut min_diff: u8 = arr.len() as u8;
    let mut i: usize = 0;

    while i < s.len()
        invariant
            0 <= i && i <= s.len(),
            min_diff as usize <= arr.len(),
            forall|p: int, q: int| (0 <= p && p < q && (q as nat) < i) && s.index(p) == s.index(q) && s.index(p) == min_val
                ==>
                (q - p) >= min_diff as int,
        decreases (s.len() as int) - (i as int)
    {
        if s.index(i as int) == min_val {
            let mut j: usize = i + 1;
            while j < s.len()
                invariant
                    i < j && j <= s.len(),
                    0 <= i && i < s.len(),
                    min_diff as usize <= arr.len(),
                    s.index(i as int) == min_val,
                    forall|p: int, q: int| (0 <= p && p < (i as int)) && ((i as nat) < q && q < (j as int)) && s.index(p) == s.index(q) && s.index(p) == min_val
                        ==>
                        (q - p) >= min_diff as int,
                    forall|q_prime: int| ((i as nat) < q_prime && q_prime < (j as int)) && s.index(i as int) == s.index(q_prime) && s.index(i as int) == min_val
                        ==>
                        (q_prime - (i as int)) >= min_diff as int,
                decreases (s.len() as int) - (j as int)
            {
                if s.index(j as int) == min_val {
                    let diff = (j - i) as u8;
                    if diff < min_diff {
                        min_diff = diff;
                    }
                }
                j = j + 1;
            }
        }
        i = i + 1;
    }
    min_diff
}
// </vc-code>


}

fn main() {}