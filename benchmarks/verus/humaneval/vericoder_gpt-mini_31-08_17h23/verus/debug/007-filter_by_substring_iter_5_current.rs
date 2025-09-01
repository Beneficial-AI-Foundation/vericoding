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

    let n: int = strings@.len() as int;
    let mut i: int = 0;
    while i < n
        invariant 0 <= i && i <= n;
        invariant forall|k: int|
            0 <= k && k < i ==>
            ( (exists|j: int|
                0 <= j &&
                j + (substring@.len() as int) <= strings@[k]@.len() as int &&
                #[trigger] (strings@[k]@.subrange(j as usize, (j + substring@.len() as int) as usize) == substring@)
            ) ==> #[trigger](res@.contains(strings@[k])));
        decreases n - i;
    {
        let s: &str = strings[i as usize];
        let s_len: int = s.len() as int;
        let sub_len: int = substring.len() as int;

        if sub_len <= s_len {
            let mut j: int = 0;
            let m: int = s_len - sub_len;
            let mut found: bool = false;
            // iterate j over 0..=m searching for match
            while j <= m && !found
                invariant 0 <= j && j <= m + 1;
                invariant (!found) ==>
                    forall|u: int| 0 <= u && u < j ==>
                        s.subrange(u as usize, (u + sub_len) as usize) != substring;
                invariant found ==>
                    exists|u: int| 0 <= u && u <= j &&
                        s.subrange(u as usize, (u + sub_len) as usize) == substring;
                decreases (m - j) + 1;
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