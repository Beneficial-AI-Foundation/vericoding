// <vc-preamble>
use vstd::prelude::*;

verus! {

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
// </vc-preamble>

// <vc-helpers>
fn exec_is_alphanumeric(c: char) -> (result: bool)
    ensures
        result == is_alphanumeric(c),
{
    c.is_ascii_alphanumeric()
}

fn exec_to_lowercase(c: char) -> (result: char)
    ensures
        result == to_lowercase(c),
{
    if c.is_ascii_uppercase() {
        (c as u8 + (b'a' - b'A')) as char
    } else {
        c
    }
}

spec fn clean(s: Seq<char>) -> Seq<char> {
    s.filter(|c: char| is_alphanumeric(c)).map(|i, c: char| to_lowercase(c))
}

/* helper modified by LLM (iteration 5): fixed compilation errors by using correct lemma names from vstd::seq_lib */
proof fn lemma_clean_distributes_add(s1: Seq<char>, s2: Seq<char>)
    ensures
        clean(s1 + s2) == clean(s1) + clean(s2),
{
    let f_filter = |c: char| is_alphanumeric(c);
    let f_map = |i: int, c: char| to_lowercase(c);
    vstd::seq_lib::lemma_filter_distributes_append(s1, s2, f_filter);
    vstd::seq_lib::lemma_map_distributes_append(s1.filter(f_filter), s2.filter(f_filter), f_map);
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
    /* code modified by LLM (iteration 5): fixed compilation errors by using correct lemma names from vstd::seq_lib */
    let bytes = s.as_bytes();
    let s_len = s.len();
    let s_spec = s@;

    if s_len == 0 {
        return true;
    }

    let mut i: usize = 0;
    let mut j: usize = s_len - 1;

    while i < j
        invariant
            s@ == s_spec,
            0 <= i < s_len,
            0 <= j < s_len,
            i <= j + 1,
            clean(s_spec.subrange(0, i as int)) == clean(s_spec.subrange(j as int + 1, s_len as int)).reverse(),
        decreases j - i,
    {
        let c_i = bytes[i] as char;
        let c_j = bytes[j] as char;

        if !exec_is_alphanumeric(c_i) {
            i = i + 1;
        } else if !exec_is_alphanumeric(c_j) {
            j = j - 1;
        } else {
            if exec_to_lowercase(c_i) != exec_to_lowercase(c_j) {
                 proof {
                    let s_prefix = s_spec.subrange(0, i as int);
                    let s_middle = s_spec.subrange(i as int, j as int + 1);
                    let s_suffix = s_spec.subrange(j as int + 1, s_len as int);

                    let clean_prefix = clean(s_prefix);
                    let clean_middle = clean(s_middle);
                    let clean_suffix = clean(s_suffix);

                    lemma_clean_distributes_add(s_prefix, s_middle + s_suffix);
                    lemma_clean_distributes_add(s_middle, s_suffix);

                    let cleaned_s = clean(s@);
                    assert(cleaned_s == clean_prefix + clean_middle + clean_suffix);

                    let c_i_seq = s_spec.subrange(i as int, i as int + 1);
                    let c_j_seq = s_spec.subrange(j as int, j as int + 1);
                    let middle_inner_seq = s_spec.subrange(i as int + 1, j as int);
                    lemma_clean_distributes_add(c_i_seq, middle_inner_seq + c_j_seq);
                    lemma_clean_distributes_add(middle_inner_seq, c_j_seq);
                    assert(is_alphanumeric(c_i)); // from loop condition
                    assert(is_alphanumeric(c_j)); // from loop condition

                    let c_i_lower = to_lowercase(c_i);
                    let c_j_lower = to_lowercase(c_j);

                    assert(clean_middle.len() > 0);
                    assert(clean_middle[0] == c_i_lower);
                    assert(clean_middle.last() == c_j_lower);
                    assert(to_lowercase(c_i) != to_lowercase(c_j));
                    assert(clean_middle[0] != clean_middle.reverse()[0]);

                    assert(cleaned_s.reverse() == (clean_prefix + clean_middle + clean_suffix).reverse());
                    vstd::seq_lib::lemma_reverse_append(clean_prefix, clean_middle + clean_suffix);
                    vstd::seq_lib::lemma_reverse_append(clean_middle, clean_suffix);
                    assert(cleaned_s.reverse() == clean_suffix.reverse() + clean_middle.reverse() + clean_prefix.reverse());

                    assert(clean(s_spec.subrange(0, i as int)) == clean_prefix);
                    assert(clean(s_spec.subrange(j as int + 1, s_len as int)) == clean_suffix);
                    let invariant_prefix = clean(s_spec.subrange(0, i as int));
                    let invariant_suffix_rev = clean(s_spec.subrange(j as int + 1, s_len as int)).reverse();
                    assert(invariant_prefix == invariant_suffix_rev); // loop invariant
                    assert(clean_prefix == clean_suffix.reverse());

                    assert(cleaned_s.reverse() == clean_prefix + clean_middle.reverse() + clean_prefix.reverse());
                    assert(cleaned_s != cleaned_s.reverse());
                }
                return false;
            }
            i = i + 1;
            j = j - 1;
        }
    }
    return true;
}
// </vc-code>

}
fn main() {}