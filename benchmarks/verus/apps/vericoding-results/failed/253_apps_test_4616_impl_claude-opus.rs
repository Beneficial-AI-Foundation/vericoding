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

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures valid_abbreviation(s@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix variable scoping issue by declaring digits at outer scope */
    let n = s.len() - 2;
    let mut result = Vec::new();
    result.push(s[0]);
    
    let mut digits = Vec::new();
    
    if n == 0 {
        result.push('0');
    } else {
        let mut m = n;
        
        // Extract digits in reverse order
        while m > 0
            invariant
                m >= 0,
                m <= n,
                n > 0,
                digits@.len() <= 100,
                forall|i: int| 0 <= i < digits@.len() ==> digits@[i] >= '0' && digits@[i] <= '9',
            decreases m
        {
            let digit = (m % 10) as u8;
            let ch = (('0' as u8) + digit) as char;
            digits.push(ch);
            m = m / 10;
        }
        
        // Add digits in correct order (reverse of extraction)
        let mut i = digits.len();
        while i > 0
            invariant
                i <= digits.len(),
                result@.len() >= 1,
                result@[0] == s@[0],
                forall|j: int| 0 <= j < digits@.len() ==> digits@[j] >= '0' && digits@[j] <= '9',
            decreases i
        {
            i = i - 1;
            result.push(digits[i]);
        }
    }
    
    result.push(s[s.len() - 1]);
    
    // Manual verification of postcondition properties
    assert(result@.len() >= 3) by {
        if n == 0 {
            assert(result@.len() == 3);
        } else {
            assert(digits@.len() >= 1);
            assert(result@.len() == 1 + digits@.len() + 1);
            assert(result@.len() >= 3);
        }
    }
    
    assert(result@[0] == s@[0]);
    assert(result@[result@.len() - 1] == s@[s@.len() - 1]);
    
    // The complex property about int_to_string equivalence requires deeper proof
    proof {
        // This would require proving that our digit extraction and reversal
        // produces the same sequence as int_to_string spec function
        // For now we need to establish this property
    }
    
    result
}
// </vc-code>


}

fn main() {}