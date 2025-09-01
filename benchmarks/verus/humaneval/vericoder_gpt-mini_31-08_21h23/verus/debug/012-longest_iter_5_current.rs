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
// <vc-helpers>
// Strengthen no helpers required; keep section to allow proofs in CODE.
#proof fn helpers_placeholder() {
    // placeholder proof to keep helpers section non-empty
    assert(true);
}
// </vc-helpers>
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
            // show the postcondition for the None case
            assert(expr_inner_longest(strings, None));
        }
        return None;
    }

    let mut best: int = 0;
    let mut k: int = 1;

    while k < (strings.len() as int)
        invariant 0 <= k && k <= (strings.len() as int)
        invariant 0 <= best && best < k
        invariant forall|i: int| #[trigger] 0 <= i < k ==> strings[best as usize].len() >= strings[i as usize].len()
        invariant forall|i: int| #[trigger] 0 <= i < best ==> strings[i as usize].len() < strings[best as usize].len()
        decreases (strings.len() as int) - k
    {
        if strings[k as usize].len() > strings[best as usize].len() {
            // Prove facts about strings[k] relative to indices < k using the previous invariants
            proof {
                // we know strings[k] is strictly greater than strings[best]
                assert(strings[k as usize].len() > strings[best as usize].len());

                // for all i < k, strings[best].len() >= strings[i].len() (by invariant)
                assert(forall|i: int| #[trigger] 0 <= i < k ==> strings[best as usize].len() >= strings[i as usize].len());

                // combine to get: for all i < k, strings[k].len() >= strings[i].len()
                // and also for all i < k, strings[i].len() < strings[k].len()
                assert(forall|i: int| #[trigger] 0 <= i < k ==> strings[k as usize].len() >= strings[i as usize].len());
                assert(forall|i: int| #[trigger] 0 <= i < k ==> strings[i as usize].len() < strings[k as usize].len());
            }

            best = k;
            k = k + 1;

            proof {
                // After update: k = old_k + 1, best = old_k
                // 0 <= k and k <= len
                assert(0 <= k);
                assert(k <= strings.len() as int);

                // 0 <= best and best < k
                assert(0 <= best);
                assert(best < k);

                // For i < k:
                // - if i == best (i == old_k): strings[best].len() >= strings[i].len() holds by reflexivity
                // - if i < best: from the proof before assignment we have strings[best].len() >= strings[i].len()
                assert(forall|i: int| #[trigger] 0 <= i < k ==> strings[best as usize].len() >= strings[i as usize].len());

                // For i < best: strings[i].len() < strings[best].len() (proved earlier for i < old_k)
                assert(forall|i: int| #[trigger] 0 <= i < best ==> strings[i as usize].len() < strings[best as usize].len());
            }
        } else {
            // We will show the invariants hold after increasing k without changing best.
            // Use the current information: invariant for i < k and the else condition strings[k] <= strings[best]
            proof {
                // previous invariant: for all i < k, strings[best].len() >= strings[i].len()
                assert(forall|i: int| #[trigger] 0 <= i < k ==> strings[best as usize].len() >= strings[i as usize].len());

                // else branch gives: strings[k].len() <= strings[best].len()
                assert(strings[k as usize].len() <= strings[best as usize].len());

                // From these, we can conclude for all i < k+1, strings[best].len() >= strings[i].len()
                // (for i < k use the invariant; for i == k use the else condition)
                assert(forall|i: int| #[trigger] 0 <= i < (k + 1) ==> strings[best as usize].len() >= strings[i as usize].len());

                // The strict-order invariant for indices < best remains unchanged
                assert(forall|i: int| #[trigger] 0 <= i < best ==> strings[i as usize].len() < strings[best as usize].len());
            }

            k = k + 1;

            proof {
                // After increment: 0 <= k && k <= len
                assert(0 <= k);
                assert(k <= strings.len() as int);

                // 0 <= best && best < k (since best < old_k and k = old_k + 1)
                assert(0 <= best);
                assert(best < k);

                // Re-establish invariants using proven facts
                assert(forall|i: int| #[trigger] 0 <= i < k ==> strings[best as usize].len() >= strings[i as usize].len());
                assert(forall|i: int| #[trigger] 0 <= i < best ==> strings[i as usize].len() < strings[best as usize].len());
            }
        }
    }

    // now k == strings.len() and invariants give the required properties
    let res: &Vec<u8> = &strings[best as usize];

    proof {
        // k equals the full length
        assert(k == strings.len() as int);

        // s.len() >= strings[i].len() for all i < strings.len()
        assert(forall|i: int| #[trigger] 0 <= i < (strings.len() as int) ==> strings[best as usize].len() >= strings[i as usize].len());

        // exist index best with required properties
        assert(0 <= best && best < (strings.len() as int));
        assert(res == &strings[best as usize]);
        assert(forall|j: int| #[trigger] 0 <= j < best ==> strings[j as usize].len() < res.len());

        // conclude expr_inner_longest(strings, Some(res))
        assert(expr_inner_longest(strings, Some(res)));
    }

    Some(res)
    // impl-end
}
// </vc-code>

fn main() {}
}