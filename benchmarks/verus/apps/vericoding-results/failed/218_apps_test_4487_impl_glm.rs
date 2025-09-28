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
/* helper modified by LLM (iteration 5): fixed character literal syntax */
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(input@)
    ensures result@ == expected_result(input@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed character literal syntax */
    let mut stripped = input.clone();
    if stripped.len() > 0 && stripped[stripped.len() - 1] == '\n' {
        stripped.pop();
    }

    let mut words: Vec<Vec<char>> = Vec::new();
    let mut start = 0;
    let mut i = 0;
    while i < stripped.len()
        invariant
            0 <= start <= i <= stripped.len(),
            forall|j: int| 0 <= j < words.len() ==> words[j].len() > 0,
    {
        if stripped[i] == ' ' {
            if start < i {
                let word = stripped[start..i].to_vec();
                words.push(word);
            }
            start = i + 1;
        }
        i = i + 1;
    }
    if start < stripped.len() {
        let word = stripped[start..].to_vec();
        words.push(word);
    }

    let result = if words.len() == 3 && words[0].len() > 0 && words[1].len() > 0 && words[2].len() > 0 {
        let a = &words[0];
        let b = &words[1];
        let c = &words[2];
        if a[a.len() - 1] == b[0] && b[b.len() - 1] == c[0] {
            vec!['Y', 'E', 'S', '\n']
        } else {
            vec!['N', 'O', '\n']
        }
    } else {
        vec![]
    };

    proof {
        assert(stripped@ == (if input@.len() > 0 && input@[input@.len() - 1] == '\n' { input@.subrange(0, input@.len() - 1) } else { input@ }));
    }

    result
}
// </vc-code>


}

fn main() {}