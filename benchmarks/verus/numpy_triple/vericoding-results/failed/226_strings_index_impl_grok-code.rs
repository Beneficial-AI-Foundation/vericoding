// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes, helper function is correct */
fn find_sub(a: Seq<char>, sub: Seq<char>, start: usize, end: usize) -> (res: usize)
    requires
        start <= end,
        end <= a.len(),
        sub.len() > 0,
        exists |i: int| start <= i <= end - sub.len() &&
        forall |j: int| 0 <= j < sub.len() ==> #[trigger] a[i + j] == sub[j],
    ensures
        start <= res <= end - sub.len(),
        forall |j: int| 0 <= j < sub.len() ==> #[trigger] a[res + j] == sub[j],
{
    /* helper modified by LLM (iteration 4): changed to executable fn using usize for casts, implemented search */
    let mut i: usize = start;
    let sub_len = sub.len();
    while i <= end - sub_len
        invariant
            start <= i <= end - sub_len + 1,
    {
        if a.subrange(i, i + sub_len) == sub {
            return i;
        }
        i = i + 1;
    }
    assert(false); // unreachable due to exists in requires
    0
}
// </vc-helpers>

// <vc-spec>
fn index(a: Vec<Seq<char>>, sub: Vec<Seq<char>>, start: Vec<i8>, end_pos: Vec<i8>) -> (result: Vec<i8>)
    requires 
        a.len() == sub.len() && sub.len() == start.len() && start.len() == end_pos.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& start[i] as int >= 0 
            &&& start[i] as int <= end_pos[i] as int
            &&& end_pos[i] as int <= a[i].len() as int
            &&& sub[i].len() > 0
        },
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            &&& result[i] as int >= 0
            &&& start[i] as int <= result[i] as int <= end_pos[i] as int
            &&& result[i] as int + sub[i].len() as int <= a[i].len() as int
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed compilation errors by removing int casts in executable code */
{
    /* code modified by LLM (iteration 4): call exec helper find_sub */
    let mut result: Vec<i8> = Vec::new();
    let mut idx: usize = 0;
    while idx < a.len()
        invariant
            0 <= (idx as int) <= a.len(),
            result.len() == idx,
            forall |i: int| 0 <= i < (idx as int) ==> {
                (start[i] as int) <= (result[i] as int) <= (end_pos[i] as int) &&
                (result[i] as int) + (sub[i].len() as int) <= (a[i].len() as int)
            }
    {
        let pos = find_sub(a[idx], sub[idx], start[idx] as usize, end_pos[idx] as usize);
        result.push(pos as i8);
        idx = idx + 1;
    }
    result
}
// </vc-code>

}
fn main() {}