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
spec fn vec_len_i<T>(v: &Vec<T>) -> int {
    v.len() as int
}
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
    if strings.len() == 0 {
        return None;
    }

    let mut best: usize = 0usize;
    let mut i: usize = 1usize;
    while i < strings.len()
        invariant
            strings.len() > 0 &&
            0 <= (best as int) && (best as int) < (strings.len() as int) &&
            1 <= (i as int) && (i as int) <= (strings.len() as int) &&
            // best is a (first) maximal index among [0, i)
            (forall|j: int| #![auto] 0 <= j && j < (i as int) ==>
                vec_len_i(&strings[best]) >= vec_len_i(&strings[j as usize])) &&
            (forall|j: int| #![auto] 0 <= j && j < (best as int) ==>
                vec_len_i(&strings[j as usize]) < vec_len_i(&strings[best]))
    {
        if strings[i].len() > strings[best].len() {
            best = i;
        }
        i = i + 1;
    }

    let res_ref: &Vec<u8> = &strings[best];

    proof {
        // At loop exit i == strings.len()
        assert((i as int) == (strings.len() as int));

        // 1) res_ref.len() >= strings[k].len() for all k in 0..strings.len()
        assert((forall|k: int| #![auto] 0 <= k && k < (strings.len() as int) ==>
            vec_len_i(res_ref) >= vec_len_i(&strings[k as usize])));

        // 2) there exists an index i (take best) such that res_ref == strings[best] and
        //    for all j < best, strings[j].len() < res_ref.len()
        assert(0 <= (best as int) && (best as int) < (strings.len() as int));
        assert(res_ref == &strings[best]);
        assert((forall|j: int| #![auto] 0 <= j && j < (best as int) ==>
            vec_len_i(&strings[j as usize]) < vec_len_i(res_ref)));
        assert(exists|idx: int|
            #![auto]
            0 <= idx && idx < (strings.len() as int) &&
            res_ref == &strings[idx as usize] &&
            (forall|j: int| #![auto] 0 <= j && j < idx ==> vec_len_i(&strings[j as usize]) < vec_len_i(res_ref))
        );
    }

    Some(res_ref)
    // impl-end
}
// </vc-code>

fn main() {}
}