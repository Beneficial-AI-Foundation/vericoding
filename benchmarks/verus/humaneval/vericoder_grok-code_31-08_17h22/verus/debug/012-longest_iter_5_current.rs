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
spec fn expr_inner_longest(strings: &Vec<Vec<u8>>, result: Option<&Vec<u8>>) -> (result: bool) {
    match result {
        None => strings.len() == 0,
        Some(s) => {
            (forall|i: int| #![auto] 0 <= i < strings.len() ==> s@.len() as int >= strings[i].len() as int)
                && (exists|i: int|
                #![auto]
                (0 <= i < strings.len() && s@ == strings[i]@ && (forall|j: int|
                    #![auto]
                    0 <= j < i ==> strings[j].len() as int < s@.len() as int)))
        },
    }
}
// pure-end

spec fn max_len_up_to(strings: &Vec<Vec<u8>>, bound: int) -> (result: nat)
    decreases bound
{
    if bound <= 0 {
        0
    } else if bound > strings.len() {
        0
    } else {
        let rest_max = max_len_up_to(strings, bound - 1);
        let candidate_len = strings[bound - 1].len() as nat;
        if candidate_len > rest_max {
            candidate_len
        } else {
            rest_max
        }
    }
}

spec fn index_of_max(strings: &Vec<Vec<u8>>, bound: int) -> (result: nat)
    decreases bound
{
    if bound <= 0 {
        0
    } else if bound > strings.len() {
        0
    } else {
        let rest_max_len = max_len_up_to(strings, bound - 1);
        let rest_index = index_of_max(strings, bound - 1);
        let candidate_len = strings[bound - 1].len() as nat;
        if candidate_len > rest_max_len {
            bound - 1
        } else {
            rest_index
        }
    }
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
    if strings.len() == 0 {
        return None;
    }
    let mut max_len: usize = 0;
    let mut max_index: usize = 0;
    let mut i: usize = 0;
    while i < strings.len() 
        invariant
            i <= strings.len(),
            i >= 1 ==> max_len as nat == max_len_up_to(strings, i as int),
            i >= 1 ==> max_index as nat == index_of_max(strings, i as int),
            i >= 1 && max_index < i,
    {
        if strings[i].len() > max_len {
            max_len = strings[i].len();
            max_index = i;
        }
        i = i + 1;
    }
    let result = &strings[max_index];
    proof {
        assert(result@.len() as nat == max_len_up_to(strings, strings.len() as int));
        assert(forall|i: int| #![auto] 0 <= i < strings.len() ==> result@.len() as int >= strings[i].len() as int);
        assert(
            exists |i: int| #![auto]
                0 <= i < strings.len() && result@ == strings[i]@ &&
                    (forall |j: int| #![auto] 0 <= j < i ==> strings[j].len() as int < result@.len() as int)
        );
    }
    Some(result)
}
// </vc-code>

fn main() {}
}