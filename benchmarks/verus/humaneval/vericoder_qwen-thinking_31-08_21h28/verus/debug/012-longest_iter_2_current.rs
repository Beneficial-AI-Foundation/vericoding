use vstd::prelude::*;

verus! {

spec fn expr_inner_longest(strings: &Vec<Vec<u8>>, result: Option<&Vec<u8>>) -> (result: bool) {
    match result {
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
// pure-end

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn longest(strings: &Vec<Vec<u8>>) -> (result: Option<&Vec<u8>>)
    // post-conditions-start
    ensures
        expr_inner_longest(strings, result),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if strings.is_empty() {
        None
    } else {
        let mut best_index = 0;
        let n = strings.len();
        for i in 1..n {
            assert(0 <= best_index < i);
            assert(forall | j: int | #![auto] 0 <= j < best_index ==> strings[j].len() < strings[best_index].len());
            assert(forall | j: int | #![auto] best_index <= j < i ==> strings[j].len() <= strings[best_index].len());
            if strings[i].len() > strings[best_index].len() {
                best_index = i;
            }
            assert(0 <= best_index < i+1);
            assert(forall | j: int | #![auto] 0 <= j < best_index ==> strings[j].len() < strings[best_index].len());
            assert(forall | j: int | #![auto] best_index <= j < i+1 ==> strings[j].len() <= strings[best_index].len());
        }
        Some(&strings[best_index])
    }
}
// </vc-code>

fn main() {}
}