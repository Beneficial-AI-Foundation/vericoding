// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(stdin_input: Seq<char>) -> bool {
    stdin_input.len() > 0 &&
    (exists|i: int| 0 <= i < stdin_input.len() && stdin_input[i] == '\n') &&
    ({
        let newline_pos = find_newline(stdin_input, 0);
        let k_str = stdin_input.subrange(0, newline_pos as int);
        is_valid_positive_integer(k_str)
    }) &&
    ({
        let newline_pos = find_newline(stdin_input, 0);
        let k_str = stdin_input.subrange(0, newline_pos as int);
        let k = string_to_int(k_str);
        1 <= k <= 100
    }) &&
    ({
        let newline_pos = find_newline(stdin_input, 0);
        let rest = stdin_input.subrange(newline_pos as int + 1, stdin_input.len() as int);
        let s = if rest.len() > 0 && rest[rest.len() - 1] == '\n' { rest.subrange(0, rest.len() - 1) } else { rest };
        1 <= s.len() <= 100 && forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 'a' && #[trigger] s[i] <= 'z'
    })
}

spec fn extract_k(stdin_input: Seq<char>) -> int
    recommends valid_input(stdin_input)
{
    let newline_pos = find_newline(stdin_input, 0);
    let k_str = stdin_input.subrange(0, newline_pos as int);
    string_to_int(k_str)
}

spec fn extract_s(stdin_input: Seq<char>) -> Seq<char>
    recommends valid_input(stdin_input)
{
    let newline_pos = find_newline(stdin_input, 0);
    let rest = stdin_input.subrange(newline_pos as int + 1, stdin_input.len() as int);
    if rest.len() > 0 && rest[rest.len() - 1] == '\n' { rest.subrange(0, rest.len() - 1) } else { rest }
}

spec fn correct_output(stdin_input: Seq<char>, result: Seq<char>) -> bool
    recommends valid_input(stdin_input)
{
    let k = extract_k(stdin_input);
    let s = extract_s(stdin_input);
    k >= 1 && k <= 100 &&
    s.len() >= 1 && s.len() <= 100 &&
    (forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 'a' && #[trigger] s[i] <= 'z') &&
    (s.len() <= k ==> result == s.add(seq!['\n'])) &&
    (s.len() > k ==> result == s.subrange(0, k).add(seq!['.', '.', '.']).add(seq!['\n']))
}

spec fn find_newline(s: Seq<char>, start: nat) -> nat
    recommends start <= s.len()
    decreases s.len() - start
{
    if start >= s.len() { 
        s.len() 
    } else if s[start as int] == '\n' { 
        start 
    } else { 
        find_newline(s, start + 1) 
    }
}

spec fn is_valid_positive_integer(s: Seq<char>) -> bool {
    s.len() > 0 && 
    (forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= '0' && #[trigger] s[i] <= '9') && 
    s != seq!['0']
}

spec fn string_to_int(s: Seq<char>) -> int
    recommends is_valid_positive_integer(s)
{
    string_to_int_helper(s, 0, 0)
}

spec fn string_to_int_helper(s: Seq<char>, pos: nat, acc: int) -> int
    recommends
        pos <= s.len(),
        acc >= 0,
        forall|i: int| 0 <= i < pos ==> #[trigger] s[i] >= '0' && #[trigger] s[i] <= '9',
        is_valid_positive_integer(s)
    decreases s.len() - pos
{
    if pos >= s.len() { 
        if acc == 0 { 1 } else { acc }
    } else if s[pos as int] >= '0' && s[pos as int] <= '9' {
        string_to_int_helper(s, pos + 1, acc * 10 + (s[pos as int] as int - '0' as int))
    } else {
        if acc == 0 { 1 } else { acc }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed parse_positive_int to handle string_to_int correctly and added overflow bounds */
fn parse_positive_int(s: &Vec<char>, start: usize, end: usize) -> (k: usize)
    requires
        start <= end,
        end <= s.len(),
        is_valid_positive_integer(s@.subrange(start as int, end as int)),
        string_to_int(s@.subrange(start as int, end as int)) <= usize::MAX
    ensures
        k == string_to_int(s@.subrange(start as int, end as int))
{
    let mut result: usize = 0;
    let mut i = start;
    
    proof {
        assert(string_to_int_helper(s@.subrange(start as int, end as int), 0, 0) == string_to_int(s@.subrange(start as int, end as int)));
    }
    
    while i < end
        invariant
            start <= i <= end,
            end <= s.len(),
            is_valid_positive_integer(s@.subrange(start as int, end as int)),
            result <= usize::MAX / 10,
            result as int == if i == start { 0 } else { string_to_int_helper(s@.subrange(start as int, i as int), 0, 0) },
            string_to_int(s@.subrange(start as int, end as int)) <= usize::MAX
        decreases end - i
    {
        let digit = (s[i] as u8) - ('0' as u8);
        proof {
            assert(digit <= 9);
            assert(result * 10 <= usize::MAX - 9);
        }
        result = result * 10 + digit as usize;
        i += 1;
    }
    
    proof {
        assert(result as int == string_to_int_helper(s@.subrange(start as int, end as int), 0, 0));
        assert(string_to_int_helper(s@.subrange(start as int, end as int), 0, 0) == string_to_int(s@.subrange(start as int, end as int)));
    }
    
    result
}

fn find_newline_exec(s: &Vec<char>, start: usize) -> (pos: usize)
    requires start <= s.len()
    ensures
        pos <= s.len(),
        pos == find_newline(s@, start as nat) as usize
{
    let mut i = start;
    
    while i < s.len()
        invariant
            start <= i <= s.len(),
            forall|j: int| start as int <= j < i ==> s@[j] != '\n',
            find_newline(s@, start as nat) == find_newline(s@, i as nat)
        decreases s.len() - i
    {
        if s[i] == '\n' {
            return i;
        }
        i += 1;
    }
    
    s.len()
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(stdin_input@)
    ensures correct_output(stdin_input@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed precondition checks and overflow issues */
    // Find the newline position
    let newline_pos = find_newline_exec(&stdin_input, 0);
    
    proof {
        // Prove that the substring is a valid positive integer
        assert(valid_input(stdin_input@));
        assert(find_newline(stdin_input@, 0) == newline_pos);
        let k_str = stdin_input@.subrange(0, newline_pos as int);
        assert(is_valid_positive_integer(k_str));
        assert(string_to_int(k_str) >= 1);
        assert(string_to_int(k_str) <= 100);
        assert(string_to_int(k_str) <= usize::MAX);
    }
    
    // Parse k from the first line
    let k = parse_positive_int(&stdin_input, 0, newline_pos);
    
    proof {
        assert(newline_pos < stdin_input.len());
        assert(newline_pos + 1 <= stdin_input.len());
    }
    
    // Calculate the start and end of string s
    let s_start = newline_pos + 1;
    let mut s_end = stdin_input.len();
    
    // Remove trailing newline from s if present
    if s_end > s_start && stdin_input[s_end - 1] == '\n' {
        s_end = s_end - 1;
    }
    
    let s_len = s_end - s_start;
    
    // Build the result
    let mut result = Vec::<char>::new();
    
    if s_len <= k {
        // Output the entire string s
        let mut i = s_start;
        while i < s_end
            invariant
                s_start <= i <= s_end,
                s_end <= stdin_input.len(),
                result.len() == i - s_start,
                forall|j: int| 0 <= j < result.len() ==> result@[j] == stdin_input@[s_start as int + j]
            decreases s_end - i
        {
            result.push(stdin_input[i]);
            i += 1;
        }
    } else {
        // Output first k characters followed by "..."
        let mut i = s_start;
        let limit = s_start + k;
        
        while i < limit
            invariant
                s_start <= i <= limit,
                limit <= s_end,
                s_end <= stdin_input.len(),
                result.len() == i - s_start,
                forall|j: int| 0 <= j < result.len() ==> result@[j] == stdin_input@[s_start as int + j]
            decreases limit - i
        {
            result.push(stdin_input[i]);
            i += 1;
        }
        
        result.push('.');
        result.push('.');
        result.push('.');
    }
    
    result.push('\n');
    result
}
// </vc-code>


}

fn main() {}