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
// none needed
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
    let n = strings.len();
    let mut i: usize = 0;
    let mut found: bool = false;
    let mut best_k: usize = 0;

    while i < n
        invariant
            n == strings.len(),
            i <= n,
            (!found ==> i == 0),
            (found ==> best_k < i),
            (found ==> forall|j: int|
                0 <= j && j < (i as int) ==> #[trigger] strings[j].len() <= strings[(best_k as int)].len()),
            (found ==> forall|j: int|
                0 <= j && j < (best_k as int) ==> #[trigger] strings[j].len() < strings[(best_k as int)].len())
        decreases n - i
    {
        let curr_len = strings[i].len();
        if !found {
            found = true;
            best_k = i;
        } else {
            let best_len_here = strings[best_k].len();
            if curr_len > best_len_here {
                best_k = i;
            }
        }
        i += 1;
    }

    assert(i == n);
    assert(n == strings.len());

    if found {
        let s_ref = &strings[best_k];

        assert((best_k as int) >= 0 && (best_k as int) < strings.len());
        assert(s_ref == strings[(best_k as int)]);
        assert(s_ref.len() == strings[(best_k as int)].len());
        assert(forall|j: int|
            0 <= j && j < strings.len() ==> #[trigger] strings[j].len() <= strings[(best_k as int)].len());

        Some(s_ref)
    } else {
        assert(n == 0);
        assert(strings.len() == 0);
        None
    }
}
// </vc-code>

fn main() {}
}