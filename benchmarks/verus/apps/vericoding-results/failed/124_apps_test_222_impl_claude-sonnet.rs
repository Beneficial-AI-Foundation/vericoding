// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn generate_squares() -> Seq<int> {
    generate_squares_helper(1, 44721)
}

spec fn is_subsequence(pattern: Seq<char>, text: Seq<char>) -> bool {
    is_subsequence_helper(pattern, text, 0, 0)
}

spec fn int_to_string(n: int) -> Seq<char> {
    if n == 0 { seq!['0'] }
    else { int_to_string_helper(n) }
}

spec fn generate_squares_helper(start: int, end: int) -> Seq<int>
    decreases end + 1 - start when start <= end
{
    if start > end { Seq::empty() }
    else { seq![start * start].add(generate_squares_helper(start + 1, end)) }
}

spec fn is_subsequence_helper(pattern: Seq<char>, text: Seq<char>, pi: int, ti: int) -> bool
    decreases pattern.len() - pi + text.len() - ti when pi <= pattern.len() && ti <= text.len()
{
    if pi >= pattern.len() { true }
    else if ti >= text.len() { false }
    else if pattern[pi] == text[ti] { 
        is_subsequence_helper(pattern, text, pi + 1, ti + 1)
    } else {
        is_subsequence_helper(pattern, text, pi, ti + 1)
    }
}

spec fn int_to_string_helper(n: int) -> Seq<char>
    decreases n when n > 0
{
    if n < 10 { seq![('0' as u8 + (n % 10) as u8) as char] }
    else { int_to_string_helper(n / 10).add(seq![('0' as u8 + (n % 10) as u8) as char]) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed old() usage in loop invariant */
fn is_subsequence_exec(pattern: &Vec<char>, text: &Vec<char>) -> (result: bool)
    requires
        pattern.len() <= usize::MAX,
        text.len() <= usize::MAX,
    ensures
        result == is_subsequence(pattern@, text@),
{
    let mut pi = 0;
    let mut ti = 0;
    
    while pi < pattern.len() && ti < text.len()
        invariant
            pi <= pattern.len(),
            ti <= text.len(),
            is_subsequence(pattern@, text@) == is_subsequence_helper(pattern@, text@, pi as int, ti as int),
        decreases text.len() - ti
    {
        if pattern[pi] == text[ti] {
            pi += 1;
        }
        ti += 1;
    }
    
    pi == pattern.len()
}

fn int_to_vec_chars(n: i32) -> (result: Vec<char>)
    requires
        n >= 0,
        n <= 2000000000,
    ensures
        result@ == int_to_string(n as int),
        result.len() <= 10,
{
    if n == 0 {
        vec!['0']
    } else {
        let mut digits = Vec::new();
        let mut num = n;
        let original_num = n;
        
        while num > 0
            invariant
                num >= 0,
                digits.len() <= 10,
                num <= original_num,
            decreases num
        {
            let digit = (num % 10) as u8;
            digits.push(('0' as u8 + digit) as char);
            num = num / 10;
        }
        
        let mut reversed = Vec::new();
        let mut idx = digits.len();
        while idx > 0
            invariant
                idx <= digits.len(),
                reversed.len() == digits.len() - idx,
            decreases idx
        {
            idx -= 1;
            reversed.push(digits[idx]);
        }
        
        proof {
            // The result should match int_to_string specification
            assert(reversed@ == int_to_string(n as int));
        }
        
        reversed
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i32)
    requires 
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> '0' <= #[trigger] s@[i] <= '9',
        s@[0] != '0' || s.len() == 1,
    ensures 
        result == -1 || result >= 0,
        result == -1 ==> forall|sq: int| #[trigger] generate_squares().contains(sq) ==> !is_subsequence(int_to_string(sq), s@),
        result >= 0 ==> exists|sq: int| #![auto] generate_squares().contains(sq) && is_subsequence(int_to_string(sq), s@) && result == s.len() as i32 - int_to_string(sq).len() as i32,
        result >= 0 ==> forall|sq: int| #[trigger] generate_squares().contains(sq) && is_subsequence(int_to_string(sq), s@) ==> s.len() as i32 - int_to_string(sq).len() as i32 >= result,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed old() usage by storing initial value */
    let mut best_result = -1;
    let mut found_valid_square = false;
    let mut witness_square: i32 = 0;
    
    let mut i: i32 = 1;
    while i <= 44721 && i * i <= 2000000000
        invariant
            1 <= i <= 44722,
            best_result == -1 || best_result >= 0,
            found_valid_square ==> (
                witness_square >= 0 &&
                witness_square <= 2000000000 &&
                generate_squares().contains(witness_square as int) &&
                is_subsequence(int_to_string(witness_square as int), s@)
            ),
            !found_valid_square ==> best_result == -1,
        decreases 44722 - i
    {
        let square = i * i;
        
        if square >= 0 && square <= 2000000000 {
            let square_str = int_to_vec_chars(square);
            
            if is_subsequence_exec(&square_str, &s) {
                #[verifier::truncate]
                let chars_removed = s.len() as i32 - square_str.len() as i32;
                if best_result == -1 || chars_removed < best_result {
                    best_result = chars_removed;
                    found_valid_square = true;
                    witness_square = square;
                }
            }
        }
        
        i += 1;
    }
    
    proof {
        if best_result >= 0 {
            // Assert that we found a valid witness
            assert(found_valid_square);
            assert(generate_squares().contains(witness_square as int));
            assert(is_subsequence(int_to_string(witness_square as int), s@));
        }
    }
    
    best_result
}
// </vc-code>


}

fn main() {}