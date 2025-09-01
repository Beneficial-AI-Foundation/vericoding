use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let substring_seq = substring@;
    let mut i = 0;
    while i < strings.len()
        invariant 0 <= i <= strings.len()
        invariant {
            forall|k: int| 0 <= k < res@.len() ==> 
                exists|idx: int| 0 <= idx < i && 
                    res@[k] == strings@[idx] && 
                    (exists|j: int| 0 <= j <= strings@[idx]@.len() - substring@.len() && strings@[idx]@.subrange(j, j + substring@.len()) == substring@)
        }
        invariant {
            forall|idx: int| 0 <= idx < i && 
                (exists|j: int| 0 <= j <= strings@[idx]@.len() - substring@.len() && strings@[idx]@.subrange(j, j + substring@.len()) == substring@) ==>
                exists|k: int| 0 <= k < res@.len() && res@[k] == strings@[idx]
        }
    {
        let s = strings[i];
        let s_seq = s@;
        let mut found = false;
        if substring_seq.len() <= s_seq.len() {
            let mut j = 0;
            while j <= s_seq.len() - substring_seq.len() && !found
                invariant 0 <= j <= s_seq.len() - substring_seq.len() + 1
                invariant found <==> (exists|k: int| 0 <= k < j && s_seq.subrange(k, k + substring_seq.len()) == substring_seq)
            {
                if s_seq.subrange(j, j + substring_seq.len()) == substring_seq {
                    found = true;
                }
                j += 1;
            }
        }
        if found {
            res.push(s);
        }
        i += 1;
    }
    res
}
// </vc-code>

fn main() {}
}