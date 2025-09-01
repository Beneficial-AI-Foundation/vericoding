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
// No additional helpers needed for this verification
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
    if (strings.len() == 0usize) {
        return None;
    }
    let mut curr_max: usize = strings[0usize].len();
    let mut curr_idx: usize = 0;
    for i in 1..strings.len()
        invariant
            forall |j: int| 0 <= j < i ==> #[trigger] (strings@[j as usize].len() <= curr_max)
            && curr_max == strings@[curr_idx as usize].len()
            && forall |j: int| 0 <= j < curr_idx ==> #[trigger] (strings@[j as usize].len() < curr_max)
            && 0 <= curr_idx < i
    {
        if (strings[i].len() > curr_max) {
            curr_max = strings[i].len();
            curr_idx = i;
        } else {
            // do nothing, curr_idx remains the leftmost
        }
    }
    let res: &Vec<u8> = &strings[curr_idx];
    assert(curr_max == res.len());
    assert(forall |k: int| 0 <= k < strings.len() ==> #[trigger] (res.len() >= strings@[k as usize].len()));
    let j: int = curr_idx as int;
    assert(0 <= j < strings.len() as int);
    assert(res == &strings@[j as usize]);
    assert(forall |k: int| 0 <= k < j ==> #[trigger] (strings@[k as usize].len() < res.len()));
    Some(res)
}
// </vc-code>

fn main() {}
}