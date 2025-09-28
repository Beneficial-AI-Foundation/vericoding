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
/* helper modified by LLM (iteration 5): convert Vec<i8> to Seq<int> */
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
{
    /* code modified by LLM (iteration 5): compute minimal distance between occurrences of sequence minimum and prove correctness */
    let s = arr_to_seq(arr);
    let min = seq_min(s);
    let n = s.len() as int;

    let mut i: int = 0;
    let mut last: int = -1;
    let mut found: bool = false;
    let mut best: int = n;
    let mut bi: int = 0;
    let mut bj: int = 0;

    while i < n
        invariant
            0 <= i <= n,
            -1 <= last < n,
            (last == -1) || (0 <= last < i && s@[last as nat] == min),
            1 <= best <= n,
            found ==> 0 <= bi < bj < i,
            found ==> s@[bi as nat] == min && s@[bj as nat] == min && best == bj - bi,
            !found ==> best == n,
            forall|p: int, q: int| 0 <= p < q < i && s@[p as nat] == min && s@[q as nat] == min ==> best <= q - p,
        decreases n - i
    {
        if s@[i as nat] == min {
            if last != -1 {
                let d = i - last;
                if !found || d < best {
                    best = d;
                    bi = last;
                    bj = i;
                    found = true;
                }
            }
            last = i;
        }
        i = i + 1;
    }

    proof {
        assert(valid_input(s));
        let (p0, q0) = choose|p0: int, q0: int| 0 <= p0 < q0 < n && s@[p0 as nat] == s@[q0 as nat] && s@[p0 as nat] == min;
        assert(forall|p: int, q: int| 0 <= p < q < n && s@[p as nat] == min && s@[q as nat] == min ==> best <= q - p);
        if !found {
            assert(best == n);
            assert(best <= q0 - p0);
            assert(q0 - p0 <= n - 1);
            assert(n <= n - 1);
            assert(false);
        }
        assert(found);
        assert(0 <= bi && bi < bj && bj < n);
        assert(s@[bi as nat] == min && s@[bj as nat] == min && best == bj - bi);
    }

    let result = best as u8;
    result
}
// </vc-code>


}

fn main() {}