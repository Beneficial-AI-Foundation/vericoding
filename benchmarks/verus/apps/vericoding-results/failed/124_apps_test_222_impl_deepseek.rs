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
proof fn lemma_int_to_string_correct(n: int)
    requires n >= 0
    ensures int_to_string(n) == (#[spec] n.to_string())
{
    /* helper modified by LLM (iteration 5): Added lemma for int_to_string correctness */
    if n == 0 {
    } else if n < 10 {
    } else {
        lemma_int_to_string_correct(n / 10);
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
    /* code modified by LLM (iteration 5): Added lemma call and verification */
    let mut min_deletions: Option<i32> = None;
    let n = s.len() as i32;
    
    proof {
        lemma_generate_squares_contains_all_squares();
        lemma_int_to_string_correct(0);
    }
    
    let mut i: int = 1;
    while i <= 44721
        invariant
            1 <= i <= 44722,
            min_deletions.is_some() ==> min_deletions.unwrap() >= 0,
            min_deletions.is_some() ==> forall|sq: int| #[trigger] generate_squares().contains(sq) && sq < i * i && is_subsequence(int_to_string(sq), s@) ==> n - int_to_string(sq).len() as i32 >= min_deletions.unwrap(),
            min_deletions.is_none() ==> forall|sq: int| #[trigger] generate_squares().contains(sq) && sq < i * i ==> !is_subsequence(int_to_string(sq), s@)
    {
        let square = i * i;
        let square_str = int_to_string(square);
        let m = square_str.len() as i32;
        
        proof {
            lemma_int_to_string_correct(square);
        }
        
        if is_subsequence(square_str, s@) {
            let deletions = n - m;
            match min_deletions {
                Some(current_min) => {
                    if deletions < current_min {
                        min_deletions = Some(deletions);
                    }
                },
                None => {
                    min_deletions = Some(deletions);
                }
            }
        }
        
        i += 1;
    }
    
    match min_deletions {
        Some(result) => result,
        None => -1
    }
}
// </vc-code>


}

fn main() {}