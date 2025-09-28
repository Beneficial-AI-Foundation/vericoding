// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type conversion for subrange arguments */
fn compare_string_sequences(s: &String, suf: &String) -> (result: bool)
    ensures result == (s@.len() >= suf@.len() && s@.subrange(s@.len() - suf@.len(), s@.len() as int) == suf@)
{
    if suf.len() > s.len() {
        false
    } else {
        let s_chars = s.as_bytes();
        let suf_chars = suf.as_bytes();
        let start = s.len() - suf.len();
        let mut i = 0;
        while i < suf.len() {
            if s_chars[start + i] != suf_chars[i] {
                proof {
                    // At the first mismatch, we know the two sequences are not equal
                    let j = start + i;
                    assert(s@.subrange(start as int, s@.len() as int) != suf@);
                }
                return false;
            }
            i += 1;
        }
        proof {
            // We have matched every character in the suffix
            assert(s@.subrange(start as int, s@.len() as int) == suf@);
        }
        true
    }
}
// </vc-helpers>

// <vc-spec>
spec fn string_ends_with(s: Seq<char>, suffix: Seq<char>) -> bool {
    if suffix.len() > s.len() {
        false
    } else {
        s.subrange(s.len() - suffix.len(), s.len() as int) == suffix
    }
}

fn endswith(a: Vec<String>, suffix: Vec<String>) -> (result: Vec<bool>)
    requires a.len() == suffix.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            /* Main specification: result matches string_ends_with for each pair */
            result[i] == string_ends_with(a[i]@, suffix[i]@) &&
            /* Mathematical property: if result is true, suffix appears at the end */
            (result[i] ==> {
                suffix[i]@.len() <= a[i]@.len() &&
                a[i]@.subrange(a[i]@.len() - suffix[i]@.len(), a[i]@.len() as int) == suffix[i]@
            }) &&
            /* Mathematical property: if result is false, suffix does not appear at the end */
            (!result[i] ==> {
                suffix[i]@.len() > a[i]@.len() ||
                a[i]@.subrange(a[i]@.len() - suffix[i]@.len(), a[i]@.len() as int) != suffix[i]@
            })
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No changes needed */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            a.len() == suffix.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                result[j] == string_ends_with(a[j]@, suffix[j]@) &&
                (result[j] ==> 
                    suffix[j]@.len() <= a[j]@.len() &&
                    a[j]@.subrange(a[j]@.len() - suffix[j]@.len(), a[j]@.len() as int) == suffix[j]@
                ) &&
                (!result[j] ==> 
                    suffix[j]@.len() > a[j]@.len() ||
                    a[j]@.subrange(a[j]@.len() - suffix[j]@.len(), a[j]@.len() as int) != suffix[j]@
                ),
        decreases a.len() - i
    {
        let s = &a[i];
        let suf = &suffix[i];
        let ends_with = compare_string_sequences(s, suf);
        result.push(ends_with);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}