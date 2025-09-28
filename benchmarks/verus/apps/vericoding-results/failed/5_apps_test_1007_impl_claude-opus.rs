// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn int_to_string(n: int) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else if n < 10 {
        seq![('0' as int + n) as char]
    } else {
        int_to_string(n / 10).add(seq![('0' as int + (n % 10)) as char])
    }
}

spec fn reverse_string(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        reverse_string(s.subrange(1, s.len() as int)).add(seq![s[0]])
    }
}

spec fn string_to_int(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.len() == 1 {
        (s[0] as int) - ('0' as int)
    } else {
        string_to_int(s.subrange(0, s.len() - 1)) * 10 + ((s[s.len() - 1] as int) - ('0' as int))
    }
}

spec fn sum_of_palindromes(k: int) -> int
    decreases k
{
    if k <= 0 {
        0
    } else if k == 1 {
        let s = int_to_string(1);
        let reversed = reverse_string(s);
        let palindrome = s.add(reversed);
        string_to_int(palindrome)
    } else {
        let s = int_to_string(k);
        let reversed = reverse_string(s);
        let palindrome = s.add(reversed);
        string_to_int(palindrome) + sum_of_palindromes(k - 1)
    }
}

spec fn valid_input(k: int, p: int) -> bool {
    k >= 1 && p >= 1
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(k: i8, p: i8) -> (result: i8)
    requires
        valid_input(k as int, p as int),
    ensures
        0 <= result < p,
        result as int == (sum_of_palindromes(k as int) % (p as int)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed initial invariant and arithmetic overflow handling */
    let mut sum: i8 = 0;
    let mut i: i8 = 1;
    
    // Establish that sum_of_palindromes(0) == 0
    assert(sum_of_palindromes(0) == 0);
    assert(sum as int == sum_of_palindromes(0) % (p as int));
    
    while i <= k
        invariant
            1 <= i <= k + 1,
            0 <= sum < p,
            sum as int == sum_of_palindromes((i - 1) as int) % (p as int),
            valid_input(k as int, p as int),
        decreases k - i
    {
        let mut n = i;
        let mut reversed: i8 = 0;
        
        while n > 0
            invariant
                0 <= n <= i,
                0 <= reversed,
                reversed <= 127,
            decreases n
        {
            if reversed <= (127 - 9) / 10 {
                reversed = reversed * 10 + (n % 10);
            }
            n = n / 10;
        }
        
        let mut n2 = i;
        let mut multiplier: i8 = 1;
        let mut temp_reversed = reversed;
        
        while temp_reversed > 0
            invariant
                0 <= temp_reversed,
                1 <= multiplier,
                multiplier <= 127,
            decreases temp_reversed
        {
            if multiplier <= 12 {
                multiplier = multiplier * 10;
            }
            temp_reversed = temp_reversed / 10;
        }
        
        // More careful overflow checking
        let mut palindrome: i8 = 0;
        if multiplier > 0 && i > 0 {
            if i <= 127 / multiplier {
                let product = i * multiplier;
                if product <= 127 - n2 {
                    palindrome = product + n2;
                }
            }
        }
        
        sum = (sum + palindrome) % p;
        i = i + 1;
    }
    
    sum
}
// </vc-code>


}
fn main() {}