// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn int_to_string(n: int) -> Seq<char>
    recommends n >= 0
{
    if n == 0 { 
        seq!['0']
    } else if n < 10 { 
        seq![('0' as int + n) as char]
    } else { 
        int_to_string(n / 10) + seq![('0' as int + (n % 10)) as char]
    }
}

spec fn reverse_string(s: Seq<char>) -> Seq<char>
{
    if s.len() == 0 { 
        seq![]
    } else { 
        reverse_string(s.subrange(1, s.len() as int)) + seq![s[0]]
    }
}

spec fn string_to_int(s: Seq<char>) -> int
    recommends s.len() > 0
{
    if s.len() == 1 { 
        (s[0] as int) - ('0' as int)
    } else { 
        string_to_int(s.subrange(0, s.len() - 1)) * 10 + ((s[s.len() - 1] as int) - ('0' as int))
    }
}

spec fn sum_of_palindromes(k: int) -> int
    recommends k >= 0
    decreases k
{
    if k == 0 { 
        0
    } else if k == 1 {
        let s = int_to_string(1);
        let reversed = reverse_string(s);
        let palindrome = s + reversed;
        string_to_int(palindrome)
    } else {
        let s = int_to_string(k);
        let reversed = reverse_string(s);
        let palindrome = s + reversed;
        string_to_int(palindrome) + sum_of_palindromes(k - 1)
    }
}

spec fn valid_input(k: int, p: int) -> bool
{
    k >= 1 && p >= 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(k: int, p: int) -> (result: int)
    requires valid_input(k, p)
    ensures 0 <= result < p
    ensures result == (sum_of_palindromes(k) % p)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}

fn main() {}