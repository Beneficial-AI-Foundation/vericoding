// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fix return binding to return result value */
fn insert_sorted(v: Vec<i32>, x: i32) -> (result: Vec<i32>)
    requires
        forall|i: int, j: int| 0 <= i < j < (v.len() as int) ==> v[i as nat] <= v[j as nat],
    ensures
        result.len() == v.len() + 1,
        forall|i: int, j: int| 0 <= i < j < (result.len() as int) ==> result[i as nat] <= result[j as nat],
        result@ =~= v@ + seq![x],
{
    let mut i: usize = 0;
    let mut res: Vec<i32> = Vec::new();
    while i < v.len() && v[i] <= x
        invariant
            i <= v.len(),
            res.len() == i,
            res@ =~= v@[0..(i as nat)],
        decreases v.len() - i
    {
        res.push(v[i]);
        i += 1;
    }
    res.push(x);
    let mut j: usize = i;
    while j < v.len()
        invariant
            i <= j,
            j <= v.len(),
            res.len() == j + 1,
            res@ =~= v@[0..(i as nat)] + seq![x] + v@[i as nat..(j as nat)],
        decreases v.len() - j
    {
        res.push(v[j]);
        j += 1;
    }
    let result = res;
    result
}

// </vc-helpers>

// <vc-spec>
fn merge_sort(list: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == list.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        result@ =~= list@,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): return final sorted vector by binding result */
    let mut res: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < list.len()
        invariant
            idx <= list.len(),
            forall|i: int, j: int| 0 <= i < j < (res.len() as int) ==> res[i as nat] <= res[j as nat],
            res@ =~= list@[0..(idx as nat)],
        decreases list.len() - idx
    {
        res = insert_sorted(res, list[idx]);
        idx += 1;
    }
    let result = res;
    result
}

// </vc-code>

}
fn main() {}