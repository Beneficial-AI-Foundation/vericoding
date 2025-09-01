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
    if strings.len() == 0 {
        None
    } else {
        let mut max_index = 0;
        let n = strings.len();
        let mut i = 1;
        while i < n {
            invariant (forall |j: nat| (j < i) ==> #[trigger] strings[j].len() <= strings[max_index].len()) &&
                      (forall |j: nat| (j < max_index) ==> #[trigger] strings[j].len() < strings[max_index].len());
            if strings[i].len() > strings[max_index].len() {
                max_index = i;
            }
            i = i + 1;
        }
        Some(&strings[max_index])
    }
}
// </vc-code>

fn main() {}
}