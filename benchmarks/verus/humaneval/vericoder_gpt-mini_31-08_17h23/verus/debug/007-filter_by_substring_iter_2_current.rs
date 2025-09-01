use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
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
    // impl-start
    let mut res: Vec<&'a str> = Vec::new();

    let mut i: int = 0;
    while i < strings@.len()
        invariant 0 <= i && i <= strings@.len();
        invariant forall|k: int| (0 <= k && k < i) ==>
            ((exists|j: int|
                0 <= j && j <= strings@[k]@.len() - substring@.len() &&
                strings@[k]@.subrange(j, #[trigger](j + substring@.len())) == substring@) ==>
             res@.contains(#[trigger](strings@[k])));
        decreases strings@.len() - i;
    {
        let s: &str = strings[i as usize];
        let s_len: int = s.len() as int;
        let sub_len: int = substring.len() as int;

        if sub_len <= s_len {
            let mut j: int = 0;
            let mut found: bool = false;
            // iterate j over 0..=s_len-sub_len searching for match
            while j <= s_len - sub_len && !found
                invariant 0 <= j && j <= s_len - sub_len + 1;
                invariant (!found) ==>
                    forall|m: int| (0 <= m && m < j) ==>
                        strings@[i]@.subrange(m, #[trigger](m + sub_len)) != substring@;
                invariant found ==>
                    exists|m: int| (0 <= m && m <= j) &&
                        strings@[i]@.subrange(m, #[trigger](m + sub_len)) == substring@;
                decreases (s_len - sub_len + 1) - j;
            {
                if s.subrange(j as usize, (j + sub_len) as usize) == substring {
                    found = true;
                } else {
                    j += 1;
                }
            }

            if found {
                res.push(s);
            }
        }

        i += 1;
    }

    res
    // impl-end
}
// </vc-code>

fn main() {}
}