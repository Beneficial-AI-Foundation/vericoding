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
spec fn my_vec_len<T>(v: &Vec<T>) -> int {
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

    let mut best: int = 0;
    let mut i: int = 1;
    while i < (strings.len() as int)
        invariant
            strings.len() > 0 &&
            0 <= best && best < (strings.len() as int) &&
            1 <= i && i <= (strings.len() as int) &&
            // best is a (first) maximal index among [0, i)
            (forall|j: int| #![auto] 0 <= j && j < i ==>
                my_vec_len(&strings[best]) >= my_vec_len(&strings[j])) &&
            (forall|j: int| #![auto] 0 <= j && j < best ==>
                my_vec_len(&strings[j]) < my_vec_len(&strings[best]))
    {
        if strings[i].len() > strings[best].len() {
            best = i;
        }
        i = i + 1;
    }

    let res_ref: &Vec<u8> = &strings[best];

    proof {
        // At loop exit i == strings.len()
        assert(i == (strings.len() as int));

        // 1) res_ref.len() >= strings[k].len() for all k in 0..strings.len()
        assert((forall|k: int| #![auto] 0 <= k && k < (strings.len() as int) ==>
            my_vec_len(res_ref) >= my_vec_len(&strings[k])));

        // 2) there exists an index i (take best) such that res_ref == strings[best] and
        //    for all j < best, strings[j].len() < res_ref.len()
        assert(0 <= best && best < (strings.len() as int));
        assert(res_ref == &strings[best]);
        assert((forall|j: int| #![auto] 0 <= j && j < best ==>
            my_vec_len(&strings[j]) < my_vec_len(res_ref)));
        assert(exists|idx: int|
            #![auto]
            0 <= idx && idx < (strings.len() as int) &&
            res_ref == &strings[idx] &&
            (forall|j: int| #![auto] 0 <= j && j < idx ==> my_vec_len(&strings[j]) < my_vec_len(res_ref))
        );
    }

    Some(res_ref)
    // impl-end
}
// </vc-code>

fn main() {}
}