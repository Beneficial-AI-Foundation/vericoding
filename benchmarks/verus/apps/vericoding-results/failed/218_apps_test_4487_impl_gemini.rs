// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0
}

spec fn valid_parsed_input(parts: Seq<Seq<char>>) -> bool {
    parts.len() == 3 && parts[0].len() > 0 && parts[1].len() > 0 && parts[2].len() > 0
}

spec fn is_word_chain(a: Seq<char>, b: Seq<char>, c: Seq<char>) -> bool {
    a.len() > 0 && b.len() > 0 && c.len() > 0 &&
    a[a.len() - 1] == b[0] && b[b.len() - 1] == c[0]
}

spec fn split_on_spaces(s: Seq<char>) -> Seq<Seq<char>>;

spec fn expected_result(input: Seq<char>) -> Seq<char> {
    let stripped = if input.len() > 0 && input[input.len() - 1] == '\n' {
        input.subrange(0, input.len() - 1)
    } else {
        input
    };
    let parts = split_on_spaces(stripped);
    if valid_parsed_input(parts) {
        if is_word_chain(parts[0], parts[1], parts[2]) {
            seq!['Y', 'E', 'S', '\n']
        } else {
            seq!['N', 'O', '\n']
        }
    } else {
        seq![]
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): removed redefinition of split_on_spaces to fix compilation error */
spec fn skip_leading_spaces(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() > 0 && s[0] == ' ' {
        skip_leading_spaces(s.subrange(1, s.len()))
    } else {
        s
    }
}

spec fn take_until_space(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() > 0 && s[0] != ' ' {
        seq![s[0]].add(take_until_space(s.subrange(1, s.len())))
    } else {
        seq![]
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(input@)
    ensures result@ == expected_result(input@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed character literal syntax error */
{
    let mut s_vec = input;
    let original_len = s_vec.len();
    let stripped_s_spec = if original_len > 0 && s_vec@.last() == '\n' {
        s_vec.pop();
        input@.subrange(0, input@.len() - 1)
    } else {
        input@
    };

    let mut parts: Vec<Vec<char>> = Vec::new();
    let mut i: usize = 0;

    while i < s_vec.len()
        invariant
            0 <= i <= s_vec.len(),
            stripped_s_spec == s_vec@,
            split_on_spaces(stripped_s_spec) == parts@.add(split_on_spaces(s_vec@.subrange(i, s_vec.len()))),
    {
        let mut word_start = i;
        while word_start < s_vec.len() && s_vec[word_start] == ' '
            invariant
                i <= word_start <= s_vec.len(),
                s_vec@.subrange(word_start, s_vec.len()) == skip_leading_spaces(s_vec@.subrange(i, s_vec.len())), 
        {
            word_start = word_start + 1;
        }

        if word_start < s_vec.len() {
            let mut word_end = word_start;
            while word_end < s_vec.len() && s_vec[word_end] != ' '
                invariant 
                    word_start <= word_end <= s_vec.len(),
                    s_vec@.subrange(word_start, word_end) == take_until_space(s_vec@.subrange(word_start, s_vec.len())),
            {
                word_end = word_end + 1;
            }
            
            let word = s_vec.sub_vec(word_start, word_end);
            parts.push(word);
            i = word_end;
        } else {
            i = s_vec.len(); 
        }
    }

    if valid_parsed_input(parts@) {
        if is_word_chain(parts[0]@, parts[1]@, parts[2]@) {
            return vec!['Y', 'E', 'S', '\n'];
        } else {
            return vec!['N', 'O', '\n'];
        }
    } else {
        return Vec::new();
    }
}
// </vc-code>


}

fn main() {}