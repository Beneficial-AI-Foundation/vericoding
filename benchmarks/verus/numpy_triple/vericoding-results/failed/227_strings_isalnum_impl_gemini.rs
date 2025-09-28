// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
#[verifier(external_body)]
fn is_alphanumeric_char_exec(c: char) -> (result: bool)
    ensures
        result == is_alphanumeric_char(c),
{
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9')
}

lemma fn lemma_all_chars_alphanumeric(s: Seq<char>)
    requires
        forall|i: int| 0 <= i < s.len() ==> is_alphanumeric_char(s[i]),
    ensures
        all_chars_alphanumeric(s),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_all_chars_alphanumeric(s.skip(1));
    }
}

lemma fn lemma_not_all_chars_alphanumeric(s: Seq<char>, k: int)
    requires
        0 <= k < s.len(),
        !is_alphanumeric_char(s[k]),
    ensures
        !all_chars_alphanumeric(s),
    decreases s.len() - k
{
  if k > 0 {
    lemma_not_all_chars_alphanumeric(s.skip(1), k - 1);
  }
}

fn check_string(s: &String) -> (res: bool)
    ensures
        res == (s@.len() > 0 && all_chars_alphanumeric(s@)),
{
    if s.len() == 0 {
        return false;
    }

    vstd::string::lemma_string_properties(s);

    let bytes = s.as_bytes();
    let mut i: usize = 0;
    while i < bytes.len()
        invariant
            vstd::string::lemma_string_properties(s),
            forall|j: int| 0 <= j < i ==> is_alphanumeric_char(s@[j]),
        decreases bytes.len() - i
    {
        let c = bytes[i] as char;
        if !is_alphanumeric_char_exec(c) {
            proof {
                let k = i as int;
                assert(s@[k] == (s.as_bytes()@)[k] as char);
                lemma_not_all_chars_alphanumeric(s@, k);
            }
            return false;
        }
        i = i + 1;
    }

    proof {
        assert forall|j: int| 0 <= j < s@.len() implies is_alphanumeric_char(s@[j]) by {
            let c = s.as_bytes()[j] as char;
            assert(is_alphanumeric_char_exec(c));
        };
        lemma_all_chars_alphanumeric(s@);
    }
    return true;
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
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == old(a).len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                result[j] == (a[j]@.len() > 0 && all_chars_alphanumeric(a[j]@)),
        decreases a.len() - i
    {
        let b = check_string(&a[i]);
        result.push(b);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}