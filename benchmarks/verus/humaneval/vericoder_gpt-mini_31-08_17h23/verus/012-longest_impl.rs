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
#[verifier(nonlinear)]
proof fn vec_index_ref_eq_spec<T>(v: &Vec<T>, i: usize)
    ensures
        v.get(i) === v.get(i),
{
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
    let n: usize = strings.len();
    if n == 0 {
        return None;
    }
    let mut best: usize = 0usize;
    let mut i: usize = 1usize;
    // loop: process indices < i; best is an index <= i that is a first-occurrence max in 0..i
    while i < n
        invariant
            i <= n,
            best < n,
            best <= i,
            // For all j in 0..i, strings@[best].len() >= strings@[j].len()
            (forall|j: int| #![trigger strings@[(best as int)].len(), strings@[j].len()] 0 <= j && j < (i as int) ==> strings@[(best as int)].len() >= strings@[j].len()),
            // For all j in 0..best, strings@[j].len() < strings@[best].len()
            (forall|j: int| #![auto] 0 <= j && j < (best as int) ==> strings@[j].len() < strings@[(best as int)].len())
    {
        if strings[i].len() > strings[best].len() {
            best = i;
        }
        i += 1;
    }
    // After loop, i == n and invariant gives best < n and maximality over all j < n
    let res: &Vec<u8> = &strings[best];
    proof {
        // From loop exit we have i == n
        assert(i == n);
        // Using the invariant with i == n gives maximality over 0..n
        assert((forall|j: int| #![auto] 0 <= j && j < (n as int) ==> strings@[(best as int)].len() >= strings@[j].len()));
        // And the first-occurrence property for indices < best
        assert((forall|j: int| #![auto] 0 <= j && j < (best as int) ==> strings@[j].len() < strings@[(best as int)].len()));
        // The chosen result equals strings@[best]
        assert(strings@[(best as int)] == *res);
        // Construct the existential required by expr_inner_longest
        assert(expr_inner_longest(strings, Some(res)));
    }
    Some(res)
    // impl-end
}
// </vc-code>

fn main() {}
}