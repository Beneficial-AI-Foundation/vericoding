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
fn to_binary_string_helper(n: nat) -> (s: String)
    requires n > 0
    ensures s@ == int_to_binary_helper(n)
    decreases n
{
    if n <= 1 {
        "1".to_string()
    } else {
        let mut s = to_binary_string_helper(n / 2);
        let old_s_seq = s@;
        let bit = if n % 2 == 1 { '1' } else { '0' };
        s.push(bit);
        proof {
            lemma_push_char_is_add(old_s_seq, bit);
        }
        s
    }
}

fn to_binary_string(n: nat) -> (s: String)
    ensures s@ == int_to_binary(n)
{
    if n == 0 {
        "0".to_string()
    } else {
        to_binary_string_helper(n)
    }
}
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
    if n > m {
        return "-1".to_string();
    }

    let count = m - n + 1;

    proof {
        if count % 2 != 0 {
            assert((m - n) % 2 == 0);
            assert(m % 2 == n % 2);
            assert((n + m) % 2 == 0);
        }
        assert((count * (n + m)) % 2 == 0);
    }
    
    let total_sum = count * (n + m) / 2;
    let quotient = total_sum / count;
    let remainder = total_sum % count;

    let rounded = if remainder * 2 < count {
        quotient
    } else if remainder * 2 > count {
        quotient + 1
    } else if quotient % 2 == 0 {
        quotient
    } else {
        quotient + 1
    };

    assert(rounded >= 1);
    let rounded_nat = rounded as nat;

    let binary_part = to_binary_string(rounded_nat);
    
    let result = format!("0b{}", binary_part);
    result
}
// </vc-code>


}

fn main() {}