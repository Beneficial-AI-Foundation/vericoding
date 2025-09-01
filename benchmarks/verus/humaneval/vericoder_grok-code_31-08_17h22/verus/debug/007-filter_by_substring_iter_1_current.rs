use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier::external_body]
fn contains_substr(s: &str, substr: &str) -> (res: bool)
    ensures
        res == exists|j: int| 0 <= j <= s@.len() - substr@.len() && s@.subrange(j, j + substr@.len()) == substr@,
{
    let s_seq = s@;
    let substr_seq = substr@;
    if substr_seq.len() == 0 {
        return true;
    }
    if s_seq.len() < substr_seq.len() {
        return false;
    }
    let mut j = 0;
    while j <= s_seq.len() - substr_seq.len()
        invariant
            0 <= j <= s_seq.len() - substr_seq.len() + 1,
            forall |k: int| 0 <= k < j ==> s_seq.subrange(k, k + substr_seq.len()) != substr_seq,
    {
        if s_seq.subrange(j, j + substr_seq.len()) == substr_seq {
            proof {
                let temp_idx = j;
                assert (exists|temp_j: int| 0 <= temp_j <= s@.len() - substr@.len() && s@.subrange(temp_j, temp_j + substr@.len()) == substr@
                    ) by { assert(temp_j == temp_idx); };
            }
            return true;
        }
        j += 1;
    }
    proof {
        assert (! (exists|j: int| 0 <= j <= s@.len() - substr@.len() && s@.subrange(j, j + substr@.len()) == substr@
            )) by { assert (forall |k: int| 0 <= k <= s@.len() - substr@.len() ==> s@.subrange(k, k + substr@.len()) != substr@
            ) by { assert (forall |k: int| 0 <= k < s@.len() - substr@.len() + 1 ==> k < s@.len() - substr@.len() + 1 && s@.subrange(k, k + substr@.len()) != substr@
                ) by { assert (forall |k: int| 0 <= k < if s@.len() >= substr@.len() { s@.len() - substr@.len() } else { 0 } ==> k < s@.len() - substr@.len() + 1 && s@.subrange(k, k + substr@.len()) != substr@
                    ) by {  }; }; }; }; };
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
{
    let mut res: Vec<&'a str> = Vec::new();
    let mut i = 0;
    while i < strings.len()
        invariant
            0 <= i <= strings@.len(),
            forall |k: int| 0 <= k < res@.len() ==> exists|j: int| 0 <= j <= strings@[res@[k] as int]@.len() - substring@.len() && strings@[res@[k] as int]@.subrange(j, j + substring@.len()) == substring@,
    {
        let s = strings[i];
        if contains_substr(s, substring) {
            assert (exists|j: int| 0 <= j <= strings@[i]@.len() - substring@.len() && strings@[i]@.subrange(j, j + substring@.len()) == substring@
            );
            res.push(s);
        }
        i += 1;
    }
    res
}
// </vc-code>

fn main() {}
}