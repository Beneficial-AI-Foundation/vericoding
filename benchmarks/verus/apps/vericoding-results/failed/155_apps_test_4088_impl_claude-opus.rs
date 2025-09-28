// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input_format(input: Seq<char>) -> bool {
    input.len() > 0
    /* TODO: Implement full validation logic for:
     * - Lines parsing and validation
     * - Test case count validation  
     * - String and integer array parsing
     * - Character and bounds validation
     */
}

spec fn valid_output_format(output: Seq<char>, input: Seq<char>) -> bool {
    valid_input_format(input) ==> output.len() > 0
    /* TODO: Implement validation for:
     * - Output lines matching test cases
     * - Correct string lengths
     * - Valid lowercase characters
     */
}

spec fn output_satisfies_constraints(output: Seq<char>, input: Seq<char>) -> bool {
    valid_input_format(input) ==> true
    /* TODO: Implement constraint validation for:
     * - Distance sum calculations
     * - Character ordering requirements
     */
}

spec fn preserves_character_usage(output: Seq<char>, input: Seq<char>) -> bool {
    valid_input_format(input) ==> true
    /* TODO: Implement character count preservation:
     * - Character frequency validation
     * - Subset usage validation
     */
}

spec fn contains_newline_terminated_results(output: Seq<char>) -> bool {
    output.len() > 0 ==> output[output.len() - 1] == '\n'
}

spec fn sum_distances_to_greater_chars(t: Seq<char>, j: int) -> int {
    0
    /* TODO: Implement distance sum calculation:
     * - Compare characters lexicographically
     * - Calculate absolute differences
     * - Sum all applicable distances
     */
}

spec fn abs_diff(i: int, j: int) -> int {
    if i >= j { i - j } else { j - i }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed ensures clause syntax */
fn next_permutation_immutable(perm: Vec<char>) -> (result: (Vec<char>, bool))
    ensures
        result.0.len() == perm.len(),
{
    if perm.len() <= 1 {
        return (perm, false);
    }
    
    let mut result = perm.clone();
    let mut i: usize = if perm.len() >= 2 { perm.len() - 2 } else { 0 };
    
    while i > 0
        invariant
            i < perm.len(),
            result.len() == perm.len(),
    {
        if result[i] < result[i + 1] {
            break;
        }
        if i == 0 {
            break;
        }
        i = i - 1;
    }
    
    if i == 0 && (perm.len() < 2 || result[0] >= result[1]) {
        return (result, false);
    }
    
    let mut j: usize = result.len() - 1;
    while j > i
        invariant
            j < result.len(),
            j >= i,
    {
        if result[j] > result[i] {
            break;
        }
        j = j - 1;
    }
    
    let temp = result[i];
    result.set(i, result[j]);
    result.set(j, temp);
    
    let mut left = i + 1;
    let mut right = result.len() - 1;
    while left < right
        invariant
            left <= right + 1,
            left <= result.len(),
            right < result.len(),
    {
        let temp = result[left];
        result.set(left, result[right]);
        result.set(right, temp);
        left = left + 1;
        if right > 0 {
            right = right - 1;
        } else {
            break;
        }
    }
    
    (result, true)
}

/* helper modified by LLM (iteration 4): Fixed ensures clause syntax */
fn sort_chars(chars: Vec<char>) -> (result: Vec<char>)
    ensures
        result.len() == chars.len(),
{
    let mut result = chars.clone();
    let n = result.len();
    
    if n == 0 {
        return result;
    }
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == n,
    {
        let mut j: usize = 0;
        while j < n - i - 1
            invariant
                j <= n - i - 1,
                i < n,
                result.len() == n,
        {
            if j + 1 < result.len() && result[j] > result[j + 1] {
                let temp = result[j];
                result.set(j, result[j + 1]);
                result.set(j + 1, temp);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: String) -> (result: String)
    requires 
        stdin_input@.len() > 0,
        valid_input_format(stdin_input@),
    ensures 
        valid_output_format(result@, stdin_input@),
        output_satisfies_constraints(result@, stdin_input@),
        preserves_character_usage(result@, stdin_input@),
        result@.len() > 0 ==> contains_newline_terminated_results(result@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): No changes needed to main code */
    let mut result = String::new();
    let lines: Vec<String> = stdin_input.split('\n').map(|s| s.to_string()).collect();
    
    if lines.len() == 0 {
        return result;
    }
    
    let t_str = if lines.len() > 0 { &lines[0] } else { return result; };
    let t_chars: Vec<char> = t_str.chars().collect();
    
    if lines.len() < 2 {
        return result;
    }
    
    let n_str = &lines[1];
    let n: usize = n_str.parse().unwrap_or(0);
    
    let mut line_idx = 2;
    let mut test_case = 0;
    
    while test_case < n
        invariant
            line_idx >= 2,
            test_case <= n,
            line_idx <= lines.len(),
    {
        if line_idx >= lines.len() {
            break;
        }
        
        let s_str = &lines[line_idx];
        let s_chars: Vec<char> = s_str.chars().collect();
        line_idx = line_idx + 1;
        
        if line_idx >= lines.len() {
            break;
        }
        
        let p_str = &lines[line_idx];
        let p_parts: Vec<&str> = p_str.split(' ').collect();
        let mut p: Vec<usize> = Vec::new();
        
        let mut part_idx = 0;
        while part_idx < p_parts.len()
            invariant
                part_idx <= p_parts.len(),
        {
            if let Ok(val) = p_parts[part_idx].parse::<usize>() {
                p.push(val);
            }
            part_idx = part_idx + 1;
        }
        line_idx = line_idx + 1;
        
        let mut best_score = i32::MAX;
        let mut best_perm = Vec::new();
        
        let mut perm = sort_chars(s_chars.clone());
        let mut has_more = true;
        
        while has_more
            invariant
                perm.len() == s_chars.len(),
        {
            let mut valid = true;
            let mut score = 0i32;
            
            let mut pi = 0;
            while pi < p.len()
                invariant
                    pi <= p.len(),
            {
                if p[pi] < perm.len() && p[pi] < t_chars.len() {
                    if perm[p[pi]] != t_chars[p[pi]] {
                        valid = false;
                        break;
                    }
                }
                pi = pi + 1;
            }
            
            if valid {
                let mut j = 0;
                while j < perm.len()
                    invariant
                        j <= perm.len(),
                {
                    let mut i = 0;
                    while i < perm.len()
                        invariant
                            i <= perm.len(),
                            j < perm.len(),
                    {
                        if perm[i] > perm[j] {
                            let diff = if i > j { i - j } else { j - i };
                            score = score + diff as i32;
                        }
                        i = i + 1;
                    }
                    j = j + 1;
                }
                
                if score < best_score {
                    best_score = score;
                    best_perm = perm.clone();
                }
            }
            
            let next_result = next_permutation_immutable(perm);
            perm = next_result.0;
            has_more = next_result.1;
        }
        
        let mut ci = 0;
        while ci < best_perm.len()
            invariant
                ci <= best_perm.len(),
        {
            result.push(best_perm[ci]);
            ci = ci + 1;
        }
        result.push('\n');
        
        test_case = test_case + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}