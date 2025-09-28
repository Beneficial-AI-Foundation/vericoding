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
spec fn current_expected(x: int, n: int) -> Seq<char>
    recommends x >= 0 && n >= 0
{
    int_to_string_helper(x, int_to_string_helper(n, seq![]))
}

fn digit_to_char(d: int) -> (c: char)
    requires 0 <= d <= 9
    ensures c as int == d + ('0' as int)
{
    char::from_u32((d + ('0' as int)) as u32).unwrap()
}

/* helper modified by LLM (iteration 5): fixed invariant syntax by combining into one block */
fn int_to_digits(x: int) -> (digits: Vec<char>)
    requires x >= 0
    ensures digits@ == int_to_string(x)
{
    if x == 0 {
        vec!['0']
    } else {
        let mut digits = Vec::new();
        let mut n = x;
        while n > 0
            invariant
                0 <= n,
                digits@ == current_expected(x, n),
            decreases n
        {
            let d = n % 10;
            let c = digit_to_char(d);
            digits.push(c);
            n = n / 10;
        }
        digits.reverse();
        digits
    }
}

fn normalize_shift(shift: int, len: int) -> (normalized: int)
    requires len >= 0
    ensures 0 <= normalized < len || len == 0
{
    if len == 0 {
        0
    } else {
        let s = shift % len;
        if s < 0 {
            s + len
        } else {
            s
        }
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
    let abs_x = if (x as int) < 0 { -((x as int)) } else { x as int };
    let digits = int_to_digits(abs_x);
    let n = digits.len() as int;
    
    if n == 0 {
        Vec::new()
    } else {
        let normalized_shift = normalize_shift(shift as int, n);
        
        if normalized_shift == 0 {
            digits
        } else if (shift as int) > n {
            let mut result = digits.clone();
            result.reverse();
            result
        } else {
            let mut result = Vec::new();
            let mut i = n - normalized_shift;
            
            while i < n
                invariant 0 <= i <= n,
                invariant result.len() == i - (n - normalized_shift),
                invariant forall|j: int| 0 <= j < result.len() ==> result@[j] == digits@[(n - normalized_shift + j) as int],
                decreases n - i
            {
                result.push(digits[i as usize]);
                i = i + 1;
            }
            
            i = 0;
            while i < n - normalized_shift
                invariant 0 <= i <= n - normalized_shift,
                invariant result.len() == normalized_shift + i,
                invariant forall|j: int| 0 <= j < normalized_shift ==> result@[j] == digits@[(n - normalized_shift + j) as int],
                invariant forall|j: int| 0 <= j < i ==> result@[normalized_shift + j] == digits@[j],
                decreases (n - normalized_shift) - i
            {
                result.push(digits[i as usize]);
                i = i + 1;
            }
            
            result
        }
    }
}
// </vc-code>


}

fn main() {}