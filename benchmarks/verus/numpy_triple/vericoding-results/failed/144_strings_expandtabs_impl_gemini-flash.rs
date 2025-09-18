// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected `exists` clause syntax in `count_chars_until_tab`. */
proof fn count_chars_until_tab(s: &str, start_idx: nat) -> (count: nat)
    requires
        start_idx <= s.len(),
    ensures
        count <= s.len() - start_idx,
        (exists i: nat where start_idx <= i < s.len() && s.byte_nth(i) == b'\t') ==> count == i - start_idx,
        (forall i: nat where start_idx <= i < start_idx + count ==> s.byte_nth(i) != b'\t'),
        (count == s.len() - start_idx ==> !(exists i: nat where start_idx <= i < s.len() && s.byte_nth(i) == b'\t'))
{
    let mut i = start_idx;
    while i < s.len()
        invariant
            start_idx <= i <= s.len(),
            forall k: nat where start_idx <= k < i ==> s.byte_nth(k) != b'\t',
    {
        if s.byte_nth(i) == b'\t' {
            return (i - start_idx) as nat;
        }
        i = i + 1;
    }
    (s.len() - start_idx) as nat
}

/* helper modified by LLM (iteration 3): Fixed compilation error by adding missing comma in exists clause */
proof fn calculate_padding(current_len: nat, tab_size: nat) -> (padding: nat)
    requires
        tab_size > 0,
    ensures
        padding < tab_size,
        (current_len + padding) % tab_size == 0,
{
    if current_len % tab_size == 0 {
        0
    } else {
        tab_size - (current_len % tab_size)
    }
}
// </vc-helpers>

// <vc-spec>
fn expandtabs(a: Vec<String>, tabsize: Vec<usize>) -> (result: Vec<String>)
    requires 
        a.len() == tabsize.len(),
        forall|i: int| 0 <= i < tabsize.len() ==> tabsize[i] > 0,
    ensures
        result.len() == a.len(),
        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> {
            let orig_str = &a[i];
            let result_str = &result[i];
            let tab_sz = tabsize[i];

            (forall|c: char| result_str@.contains(c) ==> c != '\t') &&

            (!orig_str@.contains('\t') ==> result_str@ == orig_str@) &&

            (result_str@.len() >= orig_str@.len()) &&

            (orig_str@.contains('\t') ==> result_str@.len() > orig_str@.len())
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Adjusted loop invariants for clarity and correctness */
{
    let mut result: Vec<String> = Vec::new();
    let mut i = 0;

    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            // All strings in result so far have no tabs
            forall j: int where 0 <= j < i ==> !(#[trigger]result.into_vec()[j].contains_char('\t'))
    {
        let original_str = &a[i];
        let tab_sz = tabsize[i] as nat;
        let mut current_str_chars = Seq::<char>::new();
        let mut current_column = 0nat;
        let mut j: usize = 0;

        while j < original_str.len()
            invariant
                j <= original_str.len(),
                current_str_chars.len() == current_column as int,
                // No tabs in current_str_chars
                forall k: int where 0 <= k < current_str_chars.len() ==> current_str_chars.index(k) != '\t'
        {
            let c = original_str.char_nth(j);
            if c == '\t' {
                let padding = calculate_padding(current_column, tab_sz);
                let mut k = 0;
                while k < padding
                    invariant
                        0 <= k <= padding,
                {
                    current_str_chars = current_str_chars.push(' ');
                    current_column = current_column + 1;
                    k = k + 1;
                }
            } else {
                current_str_chars = current_str_chars.push(c);
                current_column = current_column + 1;
            }
            j = j + 1;
        }
        result.push(current_str_chars.to_string());
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}