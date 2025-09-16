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
    /* code modified by LLM (iteration 4): added decreases clause to fix compilation error */
    if strings.len() == 0 {
        return None;
    }
    
    let mut longest_idx = 0;
    let mut max_len = strings[0].len();
    
    let mut i = 1;
    while i < strings.len()
        invariant
            0 <= i <= strings.len(),
            0 <= longest_idx < i,
            max_len == strings[longest_idx as int].len(),
            forall|j: int| #![auto] 0 <= j < i ==> strings[j].len() <= max_len,
            forall|j: int| #![auto] 0 <= j < longest_idx ==> strings[j].len() < max_len,
        decreases strings.len() - i
    {
        if strings[i].len() > max_len {
            longest_idx = i;
            max_len = strings[i].len();
        }
        i += 1;
    }
    
    Some(&strings[longest_idx])
}
// </vc-code>

}
fn main() {}