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
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    if strings.len() == 0 {
        return None;
    }
    
    let mut longest_idx: usize = 0;
    let mut longest_len: usize = strings[0].len();
    let mut i: usize = 1;
    
    while i < strings.len()
        invariant
            0 <= longest_idx < strings.len(),
            longest_len == strings[longest_idx as int].len(),
            forall|j: int| 0 <= j < i ==> strings[longest_idx as int].len() >= strings[j].len(),
            forall|j: int| 0 <= j < longest_idx ==> strings[j].len() < strings[longest_idx as int].len(),
            1 <= i <= strings.len(),
        decreases strings.len() - i
    {
        if strings[i].len() > longest_len {
            longest_idx = i;
            longest_len = strings[i].len();
        }
        i = i + 1;
    }
    
    Some(&strings[longest_idx])
}
// </vc-code>

}
fn main() {}