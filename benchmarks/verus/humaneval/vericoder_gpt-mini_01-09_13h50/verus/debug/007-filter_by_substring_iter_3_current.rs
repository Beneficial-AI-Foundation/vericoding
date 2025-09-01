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
            while j <= bound
                invariant 0 <= j <= bound + 1
                invariant forall|t: int| 0 <= t < j ==> s@.subrange(t, t + sub_len) != substring@
            {
                if s@.subrange(j, j + sub_len) == substring@ {
                    matched = true;
                    // exit the loop by advancing j past bound
                    j = bound + 1;
                } else {
                    j = j + 1;
                }
            }

            // Show contraposition: if not matched then there is no occurrence in [0..bound].
            proof {
                if !matched {
                    // From the loop invariants and termination, j == bound + 1
                    assert(j == bound + 1);
                    // From the invariant, for all t < j there is no match.
                    assert(forall|t: int| 0 <= t < j ==> s@.subrange(t, t + sub_len) != substring@);
                    // Hence there is no
// </vc-code>

fn main() {}
}