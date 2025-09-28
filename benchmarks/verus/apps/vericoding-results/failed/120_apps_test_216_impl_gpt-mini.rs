// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum_abs(arr: Seq<int>, i: int) -> int
    decreases arr.len() - i when 0 <= i <= arr.len()
{
    if i == arr.len() {
        0
    } else {
        (if arr[i] >= 0 { arr[i] } else { -arr[i] }) + sum_abs(arr, i + 1)
    }
}

spec fn valid_input(n: int, arr: Seq<int>) -> bool {
    0 <= n == arr.len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec equality expressing unfolding of sum_abs */
spec fn sum_abs_unfold(s: Seq<int>, i: int) -> bool
    decreases s.len() - i when 0 <= i <= s.len()
{
    sum_abs(s, i) == if i == s.len() { 0 } else { (if s[i] >= 0 { s[i] } else { -s[i] }) + sum_abs(s, i + 1) }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, arr: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, arr@.map(|i: int, v: i8| v as int))
    ensures result as int == sum_abs(arr@.map(|i: int, v: i8| v as int), 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute runtime sum with ghost invariants linking runtime and spec */
    let len: usize = arr.len();
    let mut idx: usize = 0;
    let mut acc_rt: i8 = 0;
    ghost let mut i: int = 0;
    ghost let mut acc_spec: int = 0;
    while idx < len
        invariant
            0 <= i <= len as int,
            i == idx as int,
            acc_spec == sum_abs(arr@.map(|k: int, v: i8| v as int), 0) - sum_abs(arr@.map(|k: int, v: i8| v as int), i),
            acc_rt as int == acc_spec,
        decreases
            len as int - i
    {
        let v: i8 = arr[idx];
        let add_rt: i8 = if v >= 0 { v } else { -v };
        acc_rt = acc_rt + add_rt;
        proof {
            let s = arr@.map(|k: int, v: i8| v as int);
            assert(add_rt as int == (if s@[i] >= 0 { s@[i] } else { -s@[i] }));
        }
        ghost {
            let s = arr@.map(|k: int, v: i8| v as int);
            acc_spec = acc_spec + (if s@[i] >= 0 { s@[i] } else { -s@[i] });
            i = i + 1;
        }
        idx = idx + 1;
    }
    proof {
        let s = arr@.map(|k: int, v: i8| v as int);
        assert(idx == len);
        assert(i == len as int);
        assert(acc_rt as int == sum_abs(s, 0));
    }
    acc_rt
}
// </vc-code>


}

fn main() {}