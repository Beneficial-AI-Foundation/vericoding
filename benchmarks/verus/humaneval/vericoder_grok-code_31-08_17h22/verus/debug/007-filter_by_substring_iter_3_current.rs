use vstd::prelude::*;

verus! {

// <vc-helpers>
fn contains_substr(s: &str, substr: &str) -> (res: bool)
    ensures
        res == exists|j: int| 0 <= j <= (s@.len() as int) - (substr@.len() as int) && s@.subrange(j, j + (substr@.len() as int)) == substr@,
{
    if substr.is_empty() {
        return true;
    }
    if s.len() < substr.len() {
        return false;
    }
    let mut j: int = 0;
    while j <= (s@.len() as int) - (substr@.len() as int)
        invariant
            0 <= j <= (s@.len() as int) - (substr@.len() as int) + 1,
            forall|k: int| 0 <= k < j ==> !(s@.subrange(k, k + (substr@.len() as int)) == substr@),
    {
        let start = j as usize;
        let len = substr.len();
        if &s[start..start + len] == substr {
            proof {
                assert(s@.subrange(j, j + (substr@.len() as int)) == substr@);
            }
            return true;
        }
        proof {
            assert(s@.subrange(j, j + (substr@.len() as int)) != substr@);
        }
        j += 1;
    }
    proof {
        assert(forall|k: int| 0 <= k <= (s@.len() as int) - (substr@.len() as int) ==> !(s@.subrange(k, k + (substr@.len() as int)) == substr@));
    }
    false
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
ensures
        forall|i: int|
            0 <= i < (strings@.len() as int) && (exists|j: int|
                0 <= j <= (strings@[i]@.len() as int) - (substring@.len() as int) && strings@[i]@.subrange(
                    j,
                    #[trigger] (j + (substring@.len() as int)),
                ) == substring@) ==> res@.contains(#[trigger] (strings@[i]))
{
    let mut res: Vec<&'a str> = Vec::new();
    let mut i: int = 0;
    while i < (strings@.len() as int)
        invariant
            0 <= i <= (strings@.len() as int),
            forall|k: int| 0 <= k < i && (exists|j: int|
                0 <= j <= (strings@[k as usize]@.len() as int) - (substring@.len() as int) && strings@[k as usize]@.subrange(
                    j,
                    #[trigger] (j + (substring@.len() as int)),
                ) == substring@) ==> res@.contains(#[trigger] (strings@[k as usize])),
    {
        let s = strings[i as usize];
        if contains_substr(s, substring) {
            res.push(s);
        }
        i += 1;
    }
    res
}
// </vc-code>

fn main() {}
}