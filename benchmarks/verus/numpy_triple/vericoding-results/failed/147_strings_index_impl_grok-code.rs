// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_substring_at(a: Seq<char>, sub: Seq<char>, pos: int) -> bool { 
    pos >= 0 && a.len() >= pos + sub.len() as int && a.subrange(pos as nat, pos as nat + sub.len() as nat) == sub
}
/* helper modified by LLM (iteration 5): fixed ensures syntax by wrapping condition in multi-line format to resolve compilation error */
spec fn find_start(a: Seq<char>, sub: Seq<char>, start_pos: int, end_pos: int) -> int
    requires start_pos >= 0 && start_pos <= end_pos && end_pos <= a.len() as int && sub.len() > 0 && end_pos - start_pos >= sub.len() as int
    decreases(end_pos - start_pos)
    ensures {
        start_pos <= result <= end_pos && result + sub.len() as int <= a.len() as int
    }
{
    if start_pos > end_pos {
        start_pos
    } else if is_substring_at(a, sub, start_pos) {
        start_pos
    } else {
        find_start(a, sub, start_pos + 1, end_pos)
    }
}
fn build_index_result(a: Vec<Seq<char>>, sub: Vec<Seq<char>>, start: Vec<int>, end_pos: Vec<int>, i: int) -> (result: Vec<int>)
    requires i >= 0 && i <= a.len() as int && a.len() == sub.len() && forall|j: int| j >= i && j < a.len() ==> start[j] >= 0 && start[j] <= end_pos[j] && end_pos[j] <= a[j].len() as int && sub[j].len() > 0 && end_pos[j] - start[j] >= sub[j].len() as int
    decreases((a.len() - i) as nat)
    ensures { result.len() == a.len() - i && forall|j: int| 0 <= j < result.len() ==> start[i + j] <= result[j] <= end_pos[i + j] && result[j] + sub[i + j].len() as int <= a[i + j].len() as int }
{
    if i == a.len() as int {
        Vec::new()
    } else {
        let pos = find_start(a[i], sub[i], start[i], end_pos[i]);
        let mut rest: Vec<int> = build_index_result(a, sub, start, end_pos, i + 1);
        rest.insert(0, pos);
        proof {
            assert(start[i] <= pos && pos <= end_pos[i] && pos + sub[i].len() as int <= a[i].len() as int);
            assert forall|k: int| 0 <= k < rest.len() - 1 implies (start[i + 1 + k] <= rest[k + 1] <= end_pos[i + 1 + k] && rest[k + 1] + sub[i + 1 + k].len() as int <= a[i + 1 + k].len() as int)
             by { }
        }
        rest
    }
}
// </vc-helpers>

// <vc-spec>
fn index(a: Vec<Seq<char>>, sub: Vec<Seq<char>>, start: Vec<int>, end_pos: Vec<int>) -> (result: Vec<int>)
    requires 
        a.len() == sub.len() && sub.len() == start.len() && start.len() == end_pos.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& start[i] >= 0 
            &&& start[i] <= end_pos[i]
            &&& end_pos[i] <= a[i].len() as int
            &&& sub[i].len() > 0
        },
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            &&& result[i] >= 0
            &&& start[i] <= result[i] <= end_pos[i]
            &&& result[i] + sub[i].len() as int <= a[i].len() as int
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implemented using helper function and added assertions for verification */
    build_index_result(a, sub, start, end_pos, 0)
}
// </vc-code>

}
fn main() {}