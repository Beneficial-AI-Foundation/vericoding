// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_alphanumeric_char(c: char) -> bool {
    (c >= '0' && c <= '9') || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
}

exec fn is_alphanumeric_char_exec(c: char) -> bool {
    (c >= '0' && c <= '9') || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
}
// </vc-helpers>

// <vc-spec>
spec fn is_alphanumeric_char(c: char) -> bool;

spec fn all_chars_alphanumeric(s: Seq<char>) -> bool
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        is_alphanumeric_char(s[0]) && all_chars_alphanumeric(s.skip(1))
    }
}

fn isalnum(a: Vec<String>) -> (result: Vec<bool>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            result[i] == (a[i]@.len() > 0 && all_chars_alphanumeric(a[i]@))
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<bool> = Vec::with_capacity(a.len());
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                result[j] == (a[j]@.len() > 0 && all_chars_alphanumeric(a[j]@)),
        decreases a.len() - i
    {
        let length = a[i].len();
        let chars: Vec<char> = a[i].chars().collect();
        let mut all = length > 0;
        let mut k = 0;
        while k < chars.len()
            invariant
                k <= chars.len(),
                all == (length > 0 && all_chars_alphanumeric(chars@.take((k as int)))),
            decreases chars.len() - k
        {
            all = all && is_alphanumeric_char_exec(chars[k]);
            k = k + 1;
        }
        result.push(all);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}