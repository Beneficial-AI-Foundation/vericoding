// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> s[i] == 'x' || s[i] == 'y'
}

spec fn count_char(s: Seq<char>, c: char) -> nat {
    s.filter(|x: char| x == c).len()
}

spec fn valid_output(s: Seq<char>, result: Seq<char>) -> bool 
    recommends valid_input(s)
{
    let count_x = count_char(s, 'x');
    let count_y = count_char(s, 'y');
    if count_y > count_x {
        result.len() == count_y - count_x && forall|i: int| 0 <= i < result.len() ==> result[i] == 'y'
    } else {
        result.len() == count_x - count_y && forall|i: int| 0 <= i < result.len() ==> result[i] == 'x'
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_count_char_le_len(s: Seq<char>, c: char)
    ensures count_char(s, c) <= s.len()
{
}

proof fn lemma_diff_le_len(s: Seq<char>)
    ensures
        if count_char(s, 'y') > count_char(s, 'x') {
            count_char(s, 'y') - count_char(s, 'x') <= s.len()
        } else {
            count_char(s, 'x') - count_char(s, 'y') <= s.len()
        },
{
    assert(count_char(s, 'x') <= s.len()) by { lemma_count_char_le_len(s, 'x'); };
    assert(count_char(s, 'y') <= s.len()) by { lemma_count_char_le_len(s, 'y'); };
    if count_char(s, 'y') > count_char(s, 'x') {
        assert(count_char(s, 'y') - count_char(s, 'x') <= s.len());
    } else {
        assert(count_char(s, 'x') - count_char(s, 'y') <= s.len());
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures valid_output(s@, result@)
// </vc-spec>
// <vc-code>
{
    let n = s.len();
    proof {
        lemma_diff_le_len(s@);
    }
    let make_y: bool = count_char(s@, 'y') > count_char(s@, 'x');
    let target_nat: nat = if make_y {
        count_char(s@, 'y') - count_char(s@, 'x')
    } else {
        count_char(s@, 'x') - count_char(s@, 'y')
    };
    let target_len_int: int = target_nat as int;
    assert(0 <= target_len_int);
    assert(target_len_int <= n as int);
    let target_len: usize = target_len_int as usize;

    let ch: char = if make_y { 'y' } else { 'x' };
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < target_len
        invariant
            i <= target_len,
            result.len() == i,
            forall|k: int| 0 <= k < result@.len() ==> result@[k] == ch,
        decreases (target_len as int) - (i as int)
    {
        result.push(ch);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}