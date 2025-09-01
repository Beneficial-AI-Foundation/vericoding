use vstd::prelude::*;

verus! {

// <vc-helpers>
fn contains_substring(s: &str, substr: &str) -> (res: bool)
    ensures
        (exists|j: int|
            0 <= j <= s@.len() - substr@.len() &&
            s@.subrange(j, j + substr@.len()) == substr@) ==>
        res
{
    let len_sub = substr.len();
    let n = s.len();
    if n < len_sub {
        false
    } else {
        let mut found = false;
        // invariant: found == (exists|k: int| 0 <= k < j && s.subrange(k, k + len_sub) == substr)
        for j in 0..=n - len_sub {
            if s.subrange(j, j + len_sub) == substr {
                found = true;
                break;
            }
        }
        found
    }
}
// </vc-helpers>

// <vc-spec>
fn filter_by_substring<'a>(strings: &Vec<&'a str>, substring: &str) -> (res: Vec<&'a str>)
    // post-conditions-start
    ensures
        forall|i: int|
            0 <= i < strings@.len() && (exists|j: int|
                0 <= j <= strings@[i]@.len() - substring@.len() && strings[i]@.subrange(
                    j,
                    #[trigger] (j + substring@.len()),
                ) == substring@) ==> res@.contains(#[trigger] (strings[i])),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut res = Vec::new();
    for i in 0..strings.len() {
        if contains_substring(strings[i], substring) {
            res.push(strings[i]);
        }
    }
    res
}
// </vc-code>

fn main() {}
}