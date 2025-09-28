// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 3 && s.len() <= 100 && forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 'a' && #[trigger] s[i] <= 'z'
}

spec fn valid_abbreviation(s: Seq<char>, result: Seq<char>) -> bool {
    result.len() >= 3 &&
    s.len() >= 3 &&
    result[0] == s[0] &&
    result[result.len() - 1] == s[s.len() - 1] &&
    result == seq![s[0]].add(int_to_string(s.len() - 2)).add(seq![s[s.len() - 1]])
}

spec fn int_to_string(n: int) -> Seq<char>
    decreases if n >= 0 { n } else { -n }
{
    if n == 0 {
        seq!['0']
    } else if n < 0 {
        seq!['-'].add(int_to_string_helper(-n))
    } else {
        int_to_string_helper(n)
    }
}

spec fn int_to_string_helper(n: int) -> Seq<char>
    recommends n >= 0
    decreases n
{
    if n <= 0 {
        Seq::new(0 as nat, |_i: int| ' ')
    } else {
        int_to_string_helper(n / 10).add(seq![(('0' as int) + (n % 10)) as char])
    }
}
// </vc-preamble>

// <vc-helpers>
fn vec_to_int_string(n: usize) -> (result: Vec<char>)
    ensures result@.len() >= 1,
        result@ == int_to_string(n as int)
{
    if n == 0 {
        vec!['0']
    } else {
        let mut digits = Vec::new();
        let mut num = n;
        while num > 0
            invariant num >= 0
            decreases num
        {
            let digit = (num % 10) as u8;
            let digit_char = ('0' as u8 + digit) as char;
            digits.push(digit_char);
            num = num / 10;
        }
        let mut result = Vec::new();
        let mut i = digits.len();
        while i > 0
            invariant 0 <= i <= digits.len()
            decreases i
        {
            i -= 1;
            result.push(digits[i]);
        }
        result
    }
}

/* helper modified by LLM (iteration 5): added decreases clauses */
proof fn lemma_valid_abbreviation_construction(s: Seq<char>, first: char, last: char, middle: Seq<char>)
    requires s.len() >= 3,
        first == s[0],
        last == s[s.len() - 1],
        middle == int_to_string(s.len() - 2)
    ensures valid_abbreviation(s, seq![first].add(middle).add(seq![last]))
{
}

proof fn lemma_int_string_positive(n: int)
    requires n > 0
    ensures int_to_string(n).len() >= 1
    decreases n
{
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures valid_abbreviation(s@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implementation with proper decreases clauses */
    let first = s[0];
    let last = s[s.len() - 1];
    let middle_len = s.len() - 2;
    let middle_str = vec_to_int_string(middle_len);
    
    let mut result = Vec::new();
    result.push(first);
    
    let mut i = 0;
    while i < middle_str.len()
        invariant 0 <= i <= middle_str.len(),
            result.len() == 1 + i,
            result@[0] == first,
            forall|j: int| 1 <= j < result.len() ==> result@[j] == middle_str@[j - 1]
        decreases middle_str.len() - i
    {
        result.push(middle_str[i]);
        i += 1;
    }
    
    result.push(last);
    
    proof {
        assert(result@[0] == s@[0]);
        assert(result@[result@.len() - 1] == s@[s@.len() - 1]);
        lemma_valid_abbreviation_construction(s@, first, last, middle_str@);
    }
    
    result
}
// </vc-code>


}

fn main() {}