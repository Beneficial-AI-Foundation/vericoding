// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_vowel(c: char) -> (ret:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}

spec fn vowels(s: Seq<char>) -> (ret:Seq<char>) {
    s.filter(|c| is_vowel(c))
}

spec fn inner_expr_vowels_count(s: &str, ret: u32) -> (result:bool) {
    ret == vowels(s@).len() + if (s@.len() > 0 && (s@.last() == 'y' || s@.last() == 'Y')) {
        1int

    } else {
        0int
    }
}
// </vc-preamble>

// <vc-helpers>
fn is_vowel_helper(c: char) -> bool {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}
// </vc-helpers>

// <vc-spec>
fn vowels_count(s: &str) -> (ret: u32)

    requires
        s@.len() <= u32::MAX,

    ensures
        inner_expr_vowels_count(s, ret),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected proof block to properly access last character, fixed scope issue with 'last' variable */
{
    let s_seq = s@;
    let mut count: u32 = 0;
    let mut last_char_opt: Option<char> = None;
    let len = s_seq.len() as usize;
    for i in 0..len
        invariant
            count == (s@.subrange(0, i as int).filter(|c: char| is_vowel(*c))).len() as u32,
            0 <= i <= len,
            (count as int) + 1 <= (u32::MAX as int),
    {
        let c = s_seq[i];
        if is_vowel_helper(c) {
            assert(count < u32::MAX);
            count += 1;
        }
        last_char_opt = Some(c);
    }
    let mut ret = count;
    if let Some(last) = last_char_opt {
        if last == 'y' || last == 'Y' {
            assert(ret as int + 1 <= (u32::MAX as int));
            ret += 1;
        }
    }
    proof {
        let vowels_count = (s@.filter(|c: char| is_vowel(*c))).len() as u32;
        if last_char_opt.is_none() {
            assert(count == 0);
            assert(ret == 0);
            assert(inner_expr_vowels_count(s, ret));
        } else {
            assert(last_char_opt.is_Some());
            let last = last_char_opt.unwrap();
            if last == 'y' || last == 'Y' {
                assert(ret == vowels_count + 1);
                assert(inner_expr_vowels_count(s, ret));
            } else {
                assert(ret == vowels_count);
                assert(inner_expr_vowels_count(s, ret));
            }
        }
    }
    ret
}
// </vc-code>

}
fn main() {}