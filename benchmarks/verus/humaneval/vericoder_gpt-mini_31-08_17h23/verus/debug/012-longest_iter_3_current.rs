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
// No helper lemmas needed for this proof.
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
    // impl-start
    let n: int = strings.len() as int;
    if n == 0 {
        return None;
    }
    let mut best: int = 0;
    let mut i: int = 1;
    // loop: process indices < i; best is an index <= i that is a first-occurrence max in 0..i
    while i < n
        invariant
            0 <= i && i <= n,
            0 <= best && best < n,
            best <= i,
            (forall|j: int| 0 <= j && j < i ==> strings@[best].len() >= strings@[j].len()),
            (forall|j: int| 0 <= j && j < best ==> strings@[j].len() < strings@[best].len())
    {
        if strings[i as usize].len() > strings[best as usize].len() {
            best = i;
        }
        i += 1;
    }
    // After loop, i == n and invariant gives best < n and maximality over all j < n
    let res: &Vec<u8> = &strings[best as usize];
    Some(res)
    // impl-end
}
// </vc-code>

fn main() {}
}