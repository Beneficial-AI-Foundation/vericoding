// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 2 &&
    (exists|i: int| 0 < i < input.len() && #[trigger] input[i] == ' ') &&
    (forall|i: int| 0 <= i < input.len() ==> (#[trigger] input[i] == ' ' || input[i] == '\n' || ('a' <= input[i] <= 'z'))) &&
    (exists|i: int| 0 < i < input.len() && #[trigger] input[i] == ' ' && 
     (forall|j: int| 0 <= j < i ==> #[trigger] input[j] != ' ' && input[j] != '\n') &&
     (forall|j: int| i+1 <= j < input.len() ==> #[trigger] input[j] != ' ' && input[j] != '\n'))
}

spec fn valid_output(output: Seq<char>) -> bool {
    output.len() > 0 &&
    output[output.len() as int - 1] == '\n' &&
    (forall|i: int| 0 <= i < output.len() - 1 ==> ('a' <= #[trigger] output[i] <= 'z'))
}

spec fn extract_strings(input: Seq<char>) -> (Seq<char>, Seq<char>)
    recommends valid_input(input)
{
    let space_pos = choose|space_pos: int| 0 < space_pos < input.len() && input[space_pos] == ' ' &&
                       (forall|j: int| 0 <= j < space_pos ==> #[trigger] input[j] != ' ') &&
                       (forall|j: int| space_pos+1 <= j < input.len() ==> #[trigger] input[j] != ' ' && input[j] != '\n');
    let s = input.subrange(0, space_pos);
    let t = if input[input.len() as int - 1] == '\n' { 
        input.subrange(space_pos + 1, input.len() - 1) 
    } else { 
        input.subrange(space_pos + 1, input.len() as int) 
    };
    (s, t)
}

spec fn correct_concatenation(input: Seq<char>, output: Seq<char>) -> bool
    recommends valid_input(input)
{
    let (s, t) = extract_strings(input);
    output == t.add(s).push('\n')
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): return the index of the separating space from extract_strings */
proof fn idx_from_extract(input: Seq<char>) -> int
    requires
        valid_input(input),
    ensures
        0 < result < input.len(),
        input[result] == ' ',
        (forall|j: int| 0 <= j < result ==> input[j] != ' ' && input[j] != '\n'),
        (forall|j: int| result+1 <= j < input.len() ==> input[j] != ' ' && input[j] != '\n'),
{
    let (s, _t) = extract_strings(input);
    result = s.len();
}

// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (output: Vec<char>)
    requires
        valid_input(input@),
    ensures
        valid_output(output@),
        correct_concatenation(input@, output@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): find space index via runtime scan, build output as t + s + '\n' with proofs */
    let n = input.len();

    let mut pos: usize = 0;
    while pos < n && input[pos] != ' '
        invariant
            0 <= pos <= n,
            (forall|j: int| 0 <= j < pos as int ==> input@[j] != ' ' && input@[j] != '\n'),
        decreases n - pos
    {
        pos = pos + 1;
    }

    let t_end: usize = if input[n - 1] == '\n' { n - 1 } else { n };

    let mut out: Vec<char> = Vec::new();

    let mut k: usize = pos + 1;
    while k < t_end
        invariant
            0 <= k <= t_end,
            out@ == input@.subrange(pos as int + 1, k as int),
        decreases t_end - k
    {
        out.push(input[k]);
        k = k + 1;
    }

    let mut k2: usize = 0;
    while k2 < pos
        invariant
            0 <= k2 <= pos,
            out@ == input@.subrange(pos as int + 1, t_end as int).add(input@.subrange(0, k2 as int)),
        decreases pos - k2
    {
        out.push(input[k2]);
        k2 = k2 + 1;
    }

    out.push('\n');

    proof {
        let spec_pos = idx_from_extract(input@);
        assert(forall|j: int| 0 <= j < pos as int ==> input@[j] != ' ' && input@[j] != '\n');
        assert(spec_pos < input.len());
        assert(pos as int <= spec_pos);
        assert(spec_pos <= pos as int);
        assert(pos as int == spec_pos);
        assert(out@ == input@.subrange(spec_pos + 1, t_end as int).add(input@.subrange(0, spec_pos)).push('\n'));
    }

    (out)
}

// </vc-code>


}

fn main() {}