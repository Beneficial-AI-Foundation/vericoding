// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn neg_base_2_value(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let bit_value: int = if s[s.len() - 1] == '1' { 1 } else { 0 };
        let pos = (s.len() - 1) as int;
        bit_value * spec_pow(-2, pos) + neg_base_2_value(s.drop_last())
    }
}

spec fn spec_pow(base: int, exp: int) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else if exp > 0 {
        base * spec_pow(base, exp - 1)
    } else {
        0
    }
}

spec fn is_valid_binary_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn base_neg2(n: i32) -> (result: String)
    requires n >= 0,
    ensures 
        is_valid_binary_string(result@),
        result@.len() > 0,
        neg_base_2_value(result@) == n,
        n == 0 ==> result@ == seq!['0'],
        n > 0 ==> result@[0] != '0'
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    String::new()
    // impl-end
}
// </vc-code>


}

fn main() {
    // let result1 = base_neg2(2);
    // println!("{}", result1);
    
    // let result2 = base_neg2(3);
    // println!("{}", result2);
    
    // let result3 = base_neg2(4);
    // println!("{}", result3);
}