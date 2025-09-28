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
    /* code modified by LLM (iteration 4): Added decreases clause to while loop. */
    let mut result: Vec<char> = Vec::with_capacity(s.len() + 1);
    let mut i: usize = 0;

    while i < s.len()
        invariant
            0 <= i as int,
            i <= s.len(),
            result.len() == i as int,
            forall|j: int| 0 <= j < i ==> ( (s@[j] == ',' ==> result@[j] == ' ') && (s@[j] != ',' ==> result@[j] == s@[j]) ),
        decreases s.len() - i
    {
        let c = s[i];
        if c == ',' {
            result.push(' ');
        } else {
            result.push(c);
        }
        i = i + 1;
    }

    result.push('\n');

    proof {
        assert(result.len() == (s.len() as int) + 1);
        assert(result@[s.len() as int] == '\n');
        assert(forall|k: int| 0 <= k < s.len() ==> (
            (s@[k] == ',' ==> result@[k] == ' ') && (s@[k] != ',' ==> result@[k] == s@[k])
        ));
    }

    result
}
// </vc-code>


}

fn main() {}