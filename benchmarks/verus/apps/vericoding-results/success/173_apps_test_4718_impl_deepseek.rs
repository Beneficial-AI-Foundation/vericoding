// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(date_str: Seq<char>) -> bool {
    date_str.len() == 10 && date_str.subrange(0, 4) == seq!['2', '0', '1', '7']
}

spec fn valid_output(input: Seq<char>, output: Seq<char>) -> bool 
    recommends input.len() >= 4
{
    output == seq!['2', '0', '1', '8'].add(input.subrange(4, input.len() as int)) &&
    output.len() == 10 &&
    output.subrange(0, 4) == seq!['2', '0', '1', '8'] &&
    output.subrange(4, output.len() as int) == input.subrange(4, input.len() as int)
}
// </vc-preamble>

// <vc-helpers>


spec fn valid_year_prefix(input: Seq<char>) -> Seq<char> {
    seq!['2', '0', '1', '8']
}

spec fn date_suffix(input: Seq<char>) -> Seq<char> 
    recommends input.len() >= 4
{
    input.subrange(4, input.len() as int)
}

proof fn preserved_suffix_proof(input: Seq<char>, result: Seq<char>, i: int)
    requires
        valid_input(input),
        i >= 4 && i <= input.len() as int,
        result == valid_year_prefix(input).add(input.subrange(4, i))
    ensures
        result.subrange(0, 4) == valid_year_prefix(input),
        result.subrange(4, i) == input.subrange(4, i)
{
}

// </vc-helpers>

// <vc-spec>
fn solve(date_str: Vec<char>) -> (result: Vec<char>)
    requires valid_input(date_str@)
    ensures valid_output(date_str@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed loop invariant and post-condition */
    let mut result_vec = Vec::new();
    result_vec.push('2');
    result_vec.push('0');
    result_vec.push('1');
    result_vec.push('8');
    
    proof {
        let full_input = date_str@;
        assert(full_input.len() >= 4) by {
            assert(valid_input(full_input));
        };
    }
    
    let mut i: usize = 4;
    while i < date_str.len()
        invariant
            result_vec@.len() >= 4,
            result_vec@ == valid_year_prefix(date_str@).add(date_str@.subrange(4, i as int)),
            i >= 4 && i <= date_str.len(),
        decreases date_str.len() - i
    {
        result_vec.push(date_str[i]);
        i += 1;
    }
    
    proof {
        preserved_suffix_proof(date_str@, result_vec@, date_str.len() as int);
        let suffix = date_suffix(date_str@);
        assert(result_vec@.subrange(0, 4) == valid_year_prefix(date_str@));
        assert(result_vec@.subrange(4, result_vec@.len() as int) == suffix);
        assert(valid_output(date_str@, result_vec@));
    }
    
    result_vec
}
// </vc-code>


}

fn main() {}