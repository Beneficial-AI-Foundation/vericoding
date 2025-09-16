// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn expr_inner_longest(strings: &Vec<Vec<u8>>, res: Option<&Vec<u8>>) -> (result: bool) {
    match res {
        None => strings.len() == 0,
        Some(s) => {
            (forall|i: int| #![auto] 0 <= i < strings.len() ==> s.len() >= strings[i].len())
                && (exists|i: int|
                #![auto]
                (0 <= i < strings.len() && s == strings[i] && (forall|j: int|
                    #![auto]
                    0 <= j < i ==> strings[j].len() < s.len())))
        },
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn longest(strings: &Vec<Vec<u8>>) -> (result: Option<&Vec<u8>>)

    ensures
        expr_inner_longest(strings, result),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed type errors in loop invariants by using spec indexing and casts */
    if strings.len() == 0 {
        return None;
    }

    let mut longest_so_far_idx: usize = 0;
    let mut i: usize = 1;
    while i < strings.len()
        invariant
            0 < i <= strings.len(),
            0 <= longest_so_far_idx < i,
            forall|k: int| 0 <= k < i as int ==> strings@[(longest_so_far_idx as int)].len() >= strings@[k].len(),
            forall|j: int| 0 <= j < longest_so_far_idx as int ==> strings@[j].len() < strings@[(longest_so_far_idx as int)].len(),
        decreases strings.len() - i
    {
        if strings[i].len() > strings[longest_so_far_idx].len() {
            longest_so_far_idx = i;
        }
        i = i + 1;
    }
    
    Some(&strings[longest_so_far_idx])
}
// </vc-code>

}
fn main() {}