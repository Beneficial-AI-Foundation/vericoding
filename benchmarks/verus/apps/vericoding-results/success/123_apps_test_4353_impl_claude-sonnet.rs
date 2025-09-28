// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
  s.len() == 19 && 
  s.len() >= 2 && s[5] == ',' && s[13] == ',' &&
  forall|i: int| 0 <= i < s.len() ==> (s[i] == ',' || ('a' <= s[i] <= 'z'))
}

spec fn commas_to_spaces(s: Seq<char>) -> Seq<char>
  recommends valid_input(s)
{
  Seq::new(s.len(), |i: int| { if s[i] == ',' { ' ' } else { s[i] } })
}

spec fn correct_output(s: Seq<char>, result: Seq<char>) -> bool
  recommends valid_input(s)
{
  result.len() == s.len() + 1 &&
  result[result.len() - 1] == '\n' &&
  forall|i: int| 0 <= i < s.len() ==> 
    (s[i] == ',' ==> result[i] == ' ') &&
    (s[i] != ',' ==> result[i] == s[i])
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
  requires valid_input(s@)
  ensures correct_output(s@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut result = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            valid_input(s@),
            forall|j: int| 0 <= j < i ==> (
                (s@[j] == ',' ==> result@[j] == ' ') &&
                (s@[j] != ',' ==> result@[j] == s@[j])
            ),
        decreases s.len() - i
    {
        if s[i] == ',' {
            result.push(' ');
        } else {
            result.push(s[i]);
        }
        i += 1;
    }
    result.push('\n');
    result
}
// </vc-code>


}

fn main() {}