// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_alphanumeric(c: char) -> bool {
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9')
}

spec fn to_lowercase(c: char) -> char {
    if 'A' <= c && c <= 'Z' {
        ((c as u32) + 32) as char
    } else {
        c
    }
}
// </vc-helpers>

// <vc-spec>
fn palindrome_ignore_non_alnum(s: &str) -> (result: bool)
    ensures 
        result <==> ({
            let chars_seq = s@;
            let cleaned = chars_seq.filter(|c: char| is_alphanumeric(c)).map(|i, c: char| to_lowercase(c));
            let forward = cleaned;
            let backward = cleaned.reverse();
            forward == backward
        })
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-code>


}
fn main() {
    /* Tests
    [
        {
            "input": {
                "s": ""
            },
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "s": "A man, a plan, a canal: Panama"
            },
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "s": "race a car"
            },
            "expected": false,
            "unexpected": [
                true
            ]
        },
        {
            "input": {
                "s": "No 'x' in Nixon"
            },
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "s": "abc!!cba?"
            },
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "s": "Hello, world!"
            },
            "expected": false,
            "unexpected": [
                true
            ]
        }
    ] */
}