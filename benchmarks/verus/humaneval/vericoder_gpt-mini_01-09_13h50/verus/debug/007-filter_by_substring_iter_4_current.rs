use vstd::prelude::*;

verus! {

// <vc-helpers>
// (No helpers needed)
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

    let n: int = strings@.len();
    let mut i: int = 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall|k: int|
            0 <= k < i ==>
                ( (exists|j: int|
                    0 <= j <= strings@[k]@.len() - substring@.len() &&
                    strings@[k]@.subrange(
                        j,
                        #[trigger] (j + substring@.len()),
                    ) == substring@) ==> res@.contains(strings@[k]) )
    {
        let s: &str = strings@[i];
        let s_len: int = s@.len() as int;
        let sub_len: int = substring@.len() as int;

        let mut matched: bool = false;
        if sub_len <= s_len {
            let bound: int = s_len - sub_len;
            let mut j: int = 0;
            let mut found_j: int = -1;
            while j <= bound
                invariant 0 <= j <= bound + 1
                invariant found_j >= -1 && found_j <= bound
                invariant (found_j != -1) ==> (0 <= found_j && found_j <= j - 1 && s@.subrange(found_j, found_j + sub_len) == substring@)
                invariant forall|t: int| 0 <= t < j ==> s@.subrange(t, t + sub_len) != substring@
            {
                if s@.subrange(j, j + sub_len) == substring@ {
                    matched = true;
                    found_j = j;
                    j = bound + 1;
                } else {
                    j = j + 1;
                }
            }

            proof {
                if !matched {
                    // From loop termination j == bound + 1
                    assert(j == bound + 1);
                    assert(forall|t: int| 0 <= t < j ==> s@.subrange(t, t + sub_len) != substring@);
                    // So for all t <= bound there is no match
                    assert(forall|t: int| 0 <= t <= bound ==> s@.subrange(t, t + sub_len) != substring@);
                } else {
                    // matched implies found_j != -1 and witness holds
                    assert(found_j != -1);
                    assert(0 <= found_j && found_j <= bound);
                    assert(s@.subrange(found_j, found_j + sub_len) == substring@);
                }
            }
        }

        if matched {
            res.push(s);
            proof {
                // after push, res contains s
                assert(res@.contains(s));
            }
        }

        i = i + 1;
    }

    res
    // impl-end
}
// </vc-code>

fn main() {}
}