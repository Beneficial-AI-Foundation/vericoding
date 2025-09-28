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
proof fn lemma_subrange_valid(input: Seq<char>, start: int, end: int)
    requires
        0 <= start <= end <= input.len(),
    ensures
        input.subrange(start, end).len() == end - start,
        forall|i: int| start <= i < end ==> input.subrange(start, end)[i - start] == input[i],
{
}

proof fn lemma_add_properties(s1: Seq<char>, s2: Seq<char>)
    ensures
        s1.add(s2).len() == s1.len() + s2.len(),
        forall|i: int| 0 <= i < s1.len() ==> s1.add(s2)[i] == s1[i],
        forall|i: int| s1.len() <= i < s1.add(s2).len() ==> s1.add(s2)[i] == s2[i - s1.len()],
{
}

proof fn lemma_push_properties(s: Seq<char>, c: char)
    ensures
        s.push(c).len() == s.len() + 1,
        forall|i: int| 0 <= i < s.len() ==> s.push(c)[i] == s[i],
        s.push(c)[s.len() as int] == c,
{
}

proof fn find_space_position(input: Seq<char>) -> (pos: int)
    requires
        valid_input(input),
    ensures
        0 < pos < input.len(),
        input[pos] == ' ',
        forall|j: int| 0 <= j < pos ==> input[j] != ' ',
        forall|j: int| pos+1 <= j < input.len() ==> input[j] != ' ' && input[j] != '\n',
{
    let space_pos = choose|space_pos: int| 0 < space_pos < input.len() && input[space_pos] == ' ' &&
                       (forall|j: int| 0 <= j < space_pos ==> input[j] != ' ') &&
                       (forall|j: int| space_pos+1 <= j < input.len() ==> input[j] != ' ' && input[j] != '\n');
    space_pos
}

fn vec_subrange(v: &Vec<char>, start: usize, end: usize) -> Vec<char>
    requires
        start <= end <= v.len(),
    ensures
        result@ == v@.subrange(start as int, end as int),
{
    let mut result = Vec::new();
    let mut i = start;
    while i < end
        invariant
            start <= i <= end,
            result@ == v@.subrange(start as int, i as int),
    {
        result.push(v[i]);
        i += 1;
    }
    result
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
    /* code modified by LLM (iteration 5): Fixed result reference and added proper variable declarations */
    let space_pos_int = proof {
        let pos = find_space_position(input@);
        pos
    };
    
    let space_pos: usize = space_pos_int as usize;
    let s_start: usize = 0;
    let s_end: usize = space_pos;
    let t_start: usize = space_pos + 1;
    let final_char: char = *input.last().unwrap();
    let t_end: usize = if final_char == '\n' {
        input.len() - 1
    } else {
        input.len()
    };
    
    proof {
        lemma_subrange_valid(input@, s_start as int, s_end as int);
    }
    
    proof {
        lemma_subrange_valid(input@, t_start as int, t_end as int);
    }
    
    let s_slice: Vec<char> = vec_subrange(&input, s_start, s_end);
    let t_slice: Vec<char> = vec_subrange(&input, t_start, t_end);
    
    let mut output_vec = Vec::new();
    output_vec.extend(t_slice.iter());
    output_vec.extend(s_slice.iter());
    output_vec.push('\n');
    
    proof {
        lemma_add_properties(t_slice@, s_slice@);
        lemma_push_properties(t_slice@.add(s_slice@), '\n');
    }
    
    output_vec
}
// </vc-code>


}

fn main() {}