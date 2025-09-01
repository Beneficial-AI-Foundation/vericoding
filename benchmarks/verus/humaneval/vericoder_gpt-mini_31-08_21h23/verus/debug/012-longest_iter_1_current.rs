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
// No helpers required for this proof.
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
        proof {
            // specification for None case: strings.len() == 0
        }
        return None;
    }

    let mut best: int = 0;
    let mut k: int = 1;

    while k < strings.len()
        invariant 0 <= k <= strings.len()
        invariant 0 <= best < k
        invariant forall|i: int| #[trigger] 0 <= i < k ==> strings[best].len() >= strings[i].len()
        invariant forall|i: int| #[trigger] 0 <= i < best ==> strings[i].len() < strings[best].len()
    {
        if strings[k].len() > strings[best].len() {
            best = k;
        }
        k = k + 1;
    }

    // now k == strings.len() and invariants give the required properties
    let res: &Vec<u8> = &strings[best as usize];

    proof {
        // k equals the full length
        assert(k == strings.len());

        // s.len() >= strings[i].len() for all i < strings.len()
        assert(forall|i: int| #[trigger] 0 <= i < strings.len() ==> strings[best].len() >= strings[i].len());

        // exist index best with required properties
        assert(0 <= best && best < strings.len());
        assert(res == strings[best as usize]);
        assert(forall|j: int| #[trigger] 0 <= j < best ==> strings[j].len() < res.len());

        // conclude expr_inner_longest(strings, Some(res))
    }

    Some(res)
    // impl-end
}
// </vc-code>

fn main() {}
}