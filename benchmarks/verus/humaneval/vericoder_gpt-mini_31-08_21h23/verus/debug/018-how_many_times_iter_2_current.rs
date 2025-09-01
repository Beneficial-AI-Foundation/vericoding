use vstd::prelude::*;

verus! {

spec fn how_many_times(string: Seq<char>, substring: Seq<char>) -> (result:nat)
    decreases string.len(),
{
    if (string.len() == 0) {
        0
    } else if substring.is_prefix_of(string) {
        1 + how_many_times(string.skip(1), substring)
    } else {
        how_many_times(string.skip(1), substring)
    }
}
// pure-end
// pure-end

spec fn inner_expr_how_many_times_impl(opt_k: Option<u32>, string: Vec<char>, substring: Vec<char>) -> (result:bool) {
    match opt_k {
        Some(k) => k as nat == how_many_times(string@, substring@),
        None => how_many_times(string@, substring@) > u32::MAX,
    }
}
// pure-end

// <vc-helpers>
spec fn is_prefix_at(s: Seq<char>, sub: Seq<char>, i: nat) -> bool {
    sub.is_prefix_of(s.skip(i))
}

fn vec_is_prefix_at(string: &Vec<char>, substring: &Vec<char>, start: usize) -> bool
    ensures |res: bool| res == is_prefix_at(string@, substring@, start as nat)
{
    // If substring would run past the end, cannot be a prefix.
    if start + substring.len() > string.len() {
        return false;
    }

    let mut j: nat = 0;
    while j < substring.len() as nat {
        invariant j <= substring.len() as nat;
        invariant forall |t: nat| t < j ==> string@[@(start as nat + t)] == substring@[@t];

        let c1_ref = string.get(start + j as usize);
        let c2_ref = substring.get(j as usize);
        // unwraps are safe because of bounds check above and loop condition
        let c1 = *c1_ref.unwrap();
        let c2 = *c2_ref.unwrap();

        // relate the runtime chars to the sequence views
        assert(c1 == string@[@(start as nat + j)]);
        assert(c2 == substring@[@j]);

        if c1 != c2 {
            return false;
        }

        j = j + 1;
    }

    true
}

fn rec_count(string: &Vec<char>, substring: &Vec<char>, start: usize) -> Option<u32>
    decreases string.len() - start
    ensures match result {
        Some(k) => k as nat == how_many_times(string@.skip(start as nat), substring@),
        None => how_many_times(string@.skip(start as nat), substring@) > u32::MAX,
    }
{
    if start >= string.len() {
        return Some(0);
    }

    let tail = rec_count(string, substring, start + 1);
    match tail {
        None => {
            // recursive result already overflowed, so suffix count > u32::MAX
            None
        }
        Some(t) => {
            // check whether substring is a prefix at this start position
            let ispref = vec_is_prefix_at(string, substring, start);
            if ispref {
                // if adding 1 would overflow, return None
                if t == u32::MAX {
                    None
                } else {
                    Some(t + 1)
                }
            } else {
                Some(t)
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn how_many_times_impl(string: Vec<char>, substring: Vec<char>) -> (opt_k: Option<u32>)
    // pre-conditions-start
    requires
        substring.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        inner_expr_how_many_times_impl(opt_k, string, substring),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    rec_count(&string, &substring, 0usize)
}
// </vc-code>

} // verus!
fn main() {}