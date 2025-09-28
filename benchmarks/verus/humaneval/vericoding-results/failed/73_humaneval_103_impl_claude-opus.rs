// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn int_to_binary(n: nat) -> Seq<char> {
    if n == 0 { seq!['0'] }
    else { int_to_binary_helper(n) }
}

spec fn int_to_binary_helper(n: nat) -> Seq<char>
    decreases n
{
    if n <= 1 { seq!['1'] }
    else { int_to_binary_helper(n / 2) + (if n % 2 == 1 { seq!['1'] } else { seq!['0'] }) }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn rounded_avg(n: int, m: int) -> (result: String)
    requires n > 0 && m > 0
    ensures (n > m) ==> (result@ == seq!['-', '1']) &&
            (n <= m) ==> (
        result@.len() >= 3 &&
        result@.subrange(0, 2) == seq!['0', 'b'] &&
        ({
            let count = m - n + 1;
            let total_sum = count * (n + m) / 2;
            let quotient = total_sum / count;
            let remainder = total_sum % count;
            let rounded = if remainder * 2 < count { quotient }
                         else if remainder * 2 > count { quotient + 1 }
                         else if quotient % 2 == 0 { quotient }
                         else { quotient + 1 };
            result@ == seq!['0', 'b'] + int_to_binary(rounded as nat)
        })
    )
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use i32 directly for arithmetic operations */
    if n > m {
        return "-1".to_string();
    }
    
    // Work directly with i32 values
    assert(n <= i32::MAX as int);
    assert(m <= i32::MAX as int);
    assert(n >= i32::MIN as int);
    assert(m >= i32::MIN as int);
    
    let n_i32: i32 = n as i32;
    let m_i32: i32 = m as i32;
    
    let count: i32 = m_i32 - n_i32 + 1;
    let total_sum: i32 = count * (n_i32 + m_i32) / 2;
    let quotient: i32 = total_sum / count;
    let remainder: i32 = total_sum % count;
    
    let rounded: i32 = if remainder * 2 < count {
        quotient
    } else if remainder * 2 > count {
        quotient + 1
    } else if quotient % 2 == 0 {
        quotient
    } else {
        quotient + 1
    };
    
    let mut result_str = String::new();
    result_str.push_str("0b");
    
    if rounded == 0 {
        result_str.push('0');
    } else {
        let mut temp: i32 = rounded;
        let mut binary_chars: Vec<char> = Vec::new();
        
        while temp > 0
            invariant
                temp >= 0,
                rounded > 0,
            decreases temp
        {
            if temp % 2 == 1 {
                binary_chars.push('1');
            } else {
                binary_chars.push('0');
            }
            temp = temp / 2;
        }
        
        let mut i: usize = binary_chars.len();
        while i > 0
            invariant
                i <= binary_chars.len(),
            decreases i
        {
            i = i - 1;
            result_str.push(binary_chars[i]);
        }
    }
    
    result_str
}
// </vc-code>


}

fn main() {}