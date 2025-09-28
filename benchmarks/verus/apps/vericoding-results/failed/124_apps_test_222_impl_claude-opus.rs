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
/* helper modified by LLM (iteration 3): Added trigger annotation to is_perfect_square ensures clause */
fn is_perfect_square(n: i32) -> (res: bool)
    ensures res == exists|i: int| 1 <= i <= 44721 && #[trigger] (i * i) == n as int
{
    let mut i: i32 = 1;
    while i * i < n
        invariant
            1 <= i <= 44721,
            forall|j: int| 1 <= j < i ==> j * j != n as int,
        decreases n - i * i
    {
        if i >= 44721 {
            return false;
        }
        i = i + 1;
    }
    i * i == n
}

fn parse_int(s: &Vec<char>) -> (n: i32)
    requires
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> '0' <= #[trigger] s@[i] <= '9',
        s@[0] != '0' || s.len() == 1
    ensures
        n >= 0,
        int_to_string(n as int) == s@
{
    let mut result: i32 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            result >= 0,
            result <= 2000000000,
        decreases s.len() - i
    {
        result = result * 10 + (s[i] as i32 - '0' as i32);
        i = i + 1;
    }
    result
}

fn check_subsequence(pattern: &Vec<char>, text: &Vec<char>) -> (res: bool)
    ensures res == is_subsequence(pattern@, text@)
{
    let mut pi: usize = 0;
    let mut ti: usize = 0;
    
    while pi < pattern.len() && ti < text.len()
        invariant
            pi <= pattern.len(),
            ti <= text.len(),
            is_subsequence_helper(pattern@, text@, pi as int, ti as int) == is_subsequence_helper(pattern@, text@, 0, 0),
        decreases pattern.len() - pi + text.len() - ti
    {
        if pattern[pi] == text[ti] {
            pi = pi + 1;
        }
        ti = ti + 1;
    }
    
    pi >= pattern.len()
}

fn int_to_vec(n: i32) -> (v: Vec<char>)
    requires n >= 0
    ensures v@ == int_to_string(n as int)
{
    if n == 0 {
        return vec!['0'];
    }
    
    let mut result = Vec::<char>::new();
    let mut num = n;
    let mut digits = Vec::<char>::new();
    
    while num > 0
        invariant
            num >= 0,
        decreases num
    {
        let digit = (num % 10) as u8;
        digits.push(('0' as u8 + digit) as char);
        num = num / 10;
    }
    
    let mut i: usize = digits.len();
    while i > 0
        invariant
            i <= digits.len(),
            result.len() == digits.len() - i,
        decreases i
    {
        i = i - 1;
        result.push(digits[i]);
    }
    
    result
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
    /* code modified by LLM (iteration 3): Unchanged from iteration 2 */
    let mut best: i32 = -1;
    let mut i: i32 = 1;
    
    while i <= 44721
        invariant
            1 <= i <= 44722,
            best == -1 || best >= 0,
            best == -1 ==> forall|sq: int| 1 <= sq < i && generate_squares_helper(1, sq - 1).contains(sq * sq) ==> !is_subsequence(int_to_string(sq * sq), s@),
            best >= 0 ==> exists|sq: int| 1 <= sq < i && is_subsequence(int_to_string(sq * sq), s@) && best == s.len() as i32 - int_to_string(sq * sq).len() as i32,
            best >= 0 ==> forall|sq: int| 1 <= sq < i && is_subsequence(int_to_string(sq * sq), s@) ==> s.len() as i32 - int_to_string(sq * sq).len() as i32 >= best,
        decreases 44722 - i
    {
        let square = i * i;
        let square_str = int_to_vec(square);
        
        if check_subsequence(&square_str, &s) {
            let removal_count = s.len() as i32 - square_str.len() as i32;
            if best == -1 || removal_count < best {
                best = removal_count;
            }
        }
        
        i = i + 1;
    }
    
    best
}
// </vc-code>


}

fn main() {}