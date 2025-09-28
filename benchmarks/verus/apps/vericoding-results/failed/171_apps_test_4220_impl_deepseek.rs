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

proof fn lemma_find_newline_exists(s: Seq<char>, start: nat)
    requires
        start <= s.len(),
        exists|i: int| start <= i < s.len() && s[i] == '\n'
    ensures
        find_newline(s, start) < s.len(),
        s[find_newline(s, start) as int] == '\n',
        forall|j: int| start <= j < find_newline(s, start) ==> s[j] != '\n'
    decreases s.len() - start
{
    if start < s.len() && s[start as int] != '\n' {
        lemma_find_newline_exists(s, start + 1);
    }
}

proof fn lemma_string_to_int_valid(s: Seq<char>)
    requires is_valid_positive_integer(s)
    ensures string_to_int(s) > 0
{
    lemma_string_to_int_helper_valid(s, 0, 0);
}

proof fn lemma_string_to_int_helper_valid(s: Seq<char>, pos: nat, acc: int)
    requires
        pos <= s.len(),
        acc >= 0,
        forall|i: int| 0 <= i < pos ==> #[trigger] s[i] >= '0' && #[trigger] s[i] <= '9',
        is_valid_positive_integer(s)
    ensures string_to_int_helper(s, pos, acc) > 0
    decreases s.len() - pos
{
    if pos < s.len() {
        lemma_string_to_int_helper_valid(s, pos + 1, acc * 10 + (s[pos as int] as int - '0' as int));
    }
}

/* helper modified by LLM (iteration 5): Fixed Vec subrange by converting to slice and using split_at */
fn parse_k(stdin_input: &Vec<char>) -> (k: u32)
    requires
        stdin_input@.len() > 0,
        exists|i: int| 0 <= i < stdin_input@.len() && stdin_input@[i] == '\n'
    ensures
        k as int == extract_k(stdin_input@),
        1 <= k <= 100
{
    let mut newline_pos: usize = 0;
    let mut found = false;
    let mut i: usize = 0;
    
    while i < stdin_input.len()
        invariant
            i <= stdin_input@.len(),
            newline_pos <= i,
            !found ==> (forall|j: int| 0 <= j < i ==> stdin_input@[j] != '\n'),
            found ==> (stdin_input@[newline_pos as int] == '\n' && newline_pos < i),
            found ==> newline_pos as int == find_newline(stdin_input@, 0)
        decreases stdin_input@.len() - i
    {
        if stdin_input[i] == '\n' {
            newline_pos = i;
            found = true;
            break;
        }
        i += 1;
    }
    
    proof {
        if !found {
            lemma_find_newline_exists(stdin_input@, 0);
        }
    }
    
    let k_str_slice = &stdin_input[0..newline_pos];
    let k_str: Vec<char> = k_str_slice.to_vec();
    let mut k_val: u32 = 0;
    let mut j: usize = 0;
    
    while j < k_str.len()
        invariant
            j <= k_str@.len(),
            k_val >= 0,
            k_val as int == string_to_int_helper(k_str@, 0, 0),
            forall|idx: int| 0 <= idx < j ==> #[trigger] k_str@[idx] >= '0' && #[trigger] k_str@[idx] <= '9'
        decreases k_str@.len() - j
    {
        let digit = k_str[j] as u32 - '0' as u32;
        k_val = k_val * 10 + digit;
        j += 1;
    }
    
    proof {
        lemma_string_to_int_valid(k_str@);
    }
    
    k_val
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(stdin_input@)
    ensures correct_output(stdin_input@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed Vec subrange by converting to slice and using split_at */
    let k = parse_k(&stdin_input);
    
    let mut newline_pos: usize = 0;
    let mut found = false;
    let mut i: usize = 0;
    
    while i < stdin_input.len()
        invariant
            i <= stdin_input@.len(),
            newline_pos <= i,
            !found ==> (forall|j: int| 0 <= j < i ==> stdin_input@[j] != '\n'),
            found ==> (stdin_input@[newline_pos as int] == '\n' && newline_pos < i),
            found ==> newline_pos as int == find_newline(stdin_input@, 0)
        decreases stdin_input@.len() - i
    {
        if stdin_input[i] == '\n' {
            newline_pos = i;
            found = true;
            break;
        }
        i += 1;
    }
    
    let s_start = newline_pos + 1;
    let s_end = stdin_input.len();
    let s_slice = &stdin_input[s_start..s_end];
    let mut s_chars: Vec<char> = s_slice.to_vec();
    
    if s_chars.len() > 0 && s_chars[s_chars.len() - 1] == '\n' {
        s_chars.pop();
    }
    
    if s_chars.len() <= k as usize {
        let mut result = s_chars;
        result.push('\n');
        result
    } else {
        let mut result: Vec<char> = Vec::new();
        let mut i: usize = 0;
        
        while i < k as usize
            invariant
                i <= k as usize,
                result@.len() == i,
                forall|idx: int| 0 <= idx < i ==> result@[idx] == s_chars@[idx]
            decreases k as usize - i
        {
            result.push(s_chars[i]);
            i += 1;
        }
        
        result.push('.');
        result.push('.');
        result.push('.');
        result.push('\n');
        result
    }
}
// </vc-code>


}

fn main() {}