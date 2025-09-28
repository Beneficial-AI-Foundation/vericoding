// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn int_to_string(x: int) -> Seq<char>
    recommends x >= 0
{
    if x == 0 { seq!['0'] }
    else { int_to_string_helper(x, seq![]) }
}

spec fn int_to_string_helper(x: int, acc: Seq<char>) -> Seq<char>
    recommends x >= 0
    decreases x when x >= 0
{
    if x <= 0 { acc }
    else { 
        let digit_char = ((x % 10) + ('0' as int)) as char;
        int_to_string_helper(x / 10, seq![digit_char].add(acc))
    }
}

spec fn reverse_string(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() <= 1 { s }
    else { reverse_string(s.subrange(1, s.len() as int)).add(seq![s[0]]) }
}
// </vc-preamble>

// <vc-helpers>
spec fn char_to_digit(c: char) -> int {
    (c as int) - ('0' as int)
}

spec fn digit_to_char(d: int) -> char
    requires 0 <= d <= 9
{
    ((d + ('0' as int)) as char)
}

/* helper modified by LLM (iteration 5): fixed lemma syntax by removing duplicate lemma keyword */
lemma lemma_int_to_string_length(x: int)
    requires x >= 0
    ensures int_to_string(x).len() > 0
    decreases x when x >= 0
{
    if x == 0 {
        assert(int_to_string(0) == seq!['0']);
    } else {
        lemma_int_to_string_helper_length(x, seq![]);
    }
}

lemma lemma_int_to_string_helper_length(x: int, acc: Seq<char>)
    requires x >= 0
    ensures int_to_string_helper(x, acc).len() >= acc.len()
    decreases x when x >= 0
{
    if x <= 0 {
    } else {
        let digit_char = ((x % 10) + ('0' as int)) as char;
        lemma_int_to_string_helper_length(x / 10, seq![digit_char].add(acc));
    }
}

lemma lemma_int_to_string_digits(x: int)
    requires x >= 0
    ensures forall|i: int| 0 <= i < int_to_string(x).len() ==> '0' <= int_to_string(x)[i] && int_to_string(x)[i] <= '9'
    decreases x when x >= 0
{
    if x == 0 {
        assert(int_to_string(0) == seq!['0']);
    } else {
        lemma_int_to_string_helper_digits(x, seq![]);
    }
}

lemma lemma_int_to_string_helper_digits(x: int, acc: Seq<char>)
    requires 
        x >= 0,
        forall|i: int| 0 <= i < acc.len() ==> '0' <= acc[i] && acc[i] <= '9'
    ensures forall|i: int| 0 <= i < int_to_string_helper(x, acc).len() ==> '0' <= int_to_string_helper(x, acc)[i] && int_to_string_helper(x, acc)[i] <= '9'
    decreases x when x >= 0
{
    if x <= 0 {
    } else {
        let digit = x % 10;
        let digit_char = ((digit + ('0' as int)) as char);
        assert('0' <= digit_char && digit_char <= '9');
        lemma_int_to_string_helper_digits(x / 10, seq![digit_char].add(acc));
    }
}
// </vc-helpers>

// <vc-spec>
fn circular_shift(x: i8, shift: i8) -> (result: Vec<char>)
    ensures 
        ({
            let abs_x = if (x as int) < 0 { -((x as int)) } else { x as int };
            result.len() == int_to_string(abs_x).len()
        }) &&
        ({
            let abs_x = if (x as int) < 0 { -((x as int)) } else { x as int };
            shift as int > int_to_string(abs_x).len() ==> 
                result@ == reverse_string(int_to_string(abs_x))
        }) &&
        ({
            let abs_x = if (x as int) < 0 { -((x as int)) } else { x as int };
            shift as int <= int_to_string(abs_x).len() && int_to_string(abs_x).len() > 0 ==> {
                let digits = int_to_string(abs_x);
                let n = digits.len() as int;
                let normalized_shift = (shift as int) % n;
                normalized_shift == 0 ==> result@ == digits
            }
        }) &&
        ({
            let abs_x = if (x as int) < 0 { -((x as int)) } else { x as int };
            shift as int <= int_to_string(abs_x).len() && int_to_string(abs_x).len() > 0 ==> {
                let digits = int_to_string(abs_x);
                let n = digits.len() as int;
                let normalized_shift = (shift as int) % n;
                normalized_shift > 0 ==> result@ == digits.subrange(n - normalized_shift, n).add(digits.subrange(0, n - normalized_shift))
            }
        }) &&
        (forall|i: int| 0 <= i < result.len() ==> '0' <= result[i] && result[i] <= '9')
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): same implementation as before */
    let abs_x = if x < 0 { -x } else { x };
    
    lemma_int_to_string_length(abs_x as int);
    lemma_int_to_string_digits(abs_x as int);
    
    let digits_spec = int_to_string(abs_x as int);
    let mut digits = Vec::new();
    
    let mut temp = abs_x;
    if temp == 0 {
        digits.push('0');
    } else {
        while temp > 0
            invariant
                temp >= 0,
                forall|i: int| 0 <= i < digits.len() ==> '0' <= digits[i] && digits[i] <= '9'
        {
            let digit = temp % 10;
            let digit_char = digit_to_char(digit as int);
            digits.push(digit_char);
            temp = temp / 10;
        }
        digits.reverse();
    }
    
    let n = digits.len();
    
    if shift as int > n as int {
        digits.reverse();
        return digits;
    }
    
    if n == 0 {
        return digits;
    }
    
    let normalized_shift = (shift as usize) % n;
    
    if normalized_shift == 0 {
        return digits;
    }
    
    let mut result = Vec::new();
    
    let mut i = n - normalized_shift;
    while i < n
        invariant
            n - normalized_shift <= i <= n,
            result.len() == i - (n - normalized_shift),
            forall|j: int| 0 <= j < result.len() ==> '0' <= result[j] && result[j] <= '9'
    {
        result.push(digits[i]);
        i = i + 1;
    }
    
    i = 0;
    while i < n - normalized_shift
        invariant
            0 <= i <= n - normalized_shift,
            result.len() == normalized_shift + i,
            forall|j: int| 0 <= j < result.len() ==> '0' <= result[j] && result[j] <= '9'
    {
        result.push(digits[i]);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}