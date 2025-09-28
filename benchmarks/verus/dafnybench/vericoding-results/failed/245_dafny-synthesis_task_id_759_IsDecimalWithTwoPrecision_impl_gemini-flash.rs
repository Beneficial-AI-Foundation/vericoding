use vstd::prelude::*;

verus! {

// <vc-helpers>
fn is_digit(c: char) -> bool {
    '0' <= c && c <= '9'
}

// A helper function to find the last occurrence of an element in a sequence.
proof fn seq_find_last<V>(s: Seq<V>, pred: spec_fn(V) -> bool) -> (result: Option<nat>)
    ensures
        match result {
            Some(idx) =>
                idx < s.len() && pred(s[idx]) &&
                forall|k: nat| idx < k < s.len() ==> !pred(s[k]),
            None => forall|k: nat| k < s.len() ==> !pred(s[k]),
        },
{
    let mut i = s.len();
    while i > 0
        invariant
            0 <= i <= s.len(),
            forall|k: nat| i <= k < s.len() ==> !pred(s[k]),
    {
        i = i - 1;
        if pred(s[i]) {
            return Some(i);
        }
    }
    None
}

fn check_decimal_with_two_precision_internal(s: &str) -> (result: (bool, Option<usize>))
    ensures
        s.len() == 0 ==> result == (false, None),
        result.0 ==> exists|i: int| 0 <= i < s@.len() as int && s@[i] == '.',
        result.0 ==> (result.1.is_Some() && (s@.len() as int - result.1.unwrap() as int - 1 == 2)),
        !result.0 ==> !exists|i: int| 0 <= i < s@.len() as int && s@[i] == '.' || 
                     ! (exists|i: int| 0 <= i < s@.len() as int && s@[i] == '.' && (s@.len() as int - i - 1 == 2)),
{
    let mut num_dots = 0;
    let mut dot_index: Option<usize> = None;
    let s_bytes = s.as_bytes();

    let mut i = 0;
    while i < s_bytes.len()
        invariant
            0 <= i as int <= s_bytes.len() as int,
            num_dots == (if exists|k: int| 0 <= k < i as int && s_bytes@.index(k) == b'.' { 1 } else { 0 }),
            dot_index.is_Some() == (exists|k: int| 0 <= k < i as int && s_bytes@.index(k) == b'.'),
            dot_index.is_Some() ==> dot_index.unwrap() as int == (
                proof {
                    let s_seq = s_bytes.reveal_as_seq();
                    let sub_s_seq = s_seq.subsequence(0 as nat, i as nat);
                    let last_dot_idx = seq_find_last(sub_s_seq, |c: u8| c == b'.');
                    assert(last_dot_idx.is_Some());
                }
                seq_find_last(s_bytes.reveal_as_seq().subsequence(0 as nat, i as nat), |c: u8| c == b'.').unwrap() as int
            ),
            forall|k: int| 0 <= k < i as int && s_bytes@.index(k) != b'.' ==> is_digit(s_bytes@.index(k) as char),
    {
        let c = s_bytes@.index(i as int);
        if c == b'.' {
            num_dots = num_dots + 1;
            dot_index = Some(i as usize);
        } else if !is_digit(c as char) {
            return (false, None);
        }
        i = i + 1;
    }

    if num_dots == 1 {
        if let Some(dot_idx_usize) = dot_index {
            if dot_idx_usize < s_bytes.len() { 
                let digits_after_dot = s_bytes.len() - 1 - dot_idx_usize;
                if digits_after_dot == 2 {
                    return (true, Some(dot_idx_usize));
                }
            }
        }
    }
    (false, None)
}
// </vc-helpers>

// <vc-spec>
fn is_decimal_with_two_precision(s: &str) -> (result: bool)
    ensures
        result ==> exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
        !result ==> !exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
// </vc-spec>
// <vc-code>
{
    let (is_dec, dot_idx_opt) = check_decimal_with_two_precision_internal(s);
    is_dec
}
// </vc-code>

fn main() {
}

}