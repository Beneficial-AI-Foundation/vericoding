// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): changed to return &str for push_str compatibility */
fn digit_to_str(d: u8) -> (s: &'static str)
    requires d < 10
    ensures 
        s@.len() == 1,
        s@[0] as int == '0' as int + d as int,
{
    if d == 0 { "0" }
    else if d == 1 { "1" }
    else if d == 2 { "2" }
    else if d == 3 { "3" }
    else if d == 4 { "4" }
    else if d == 5 { "5" }
    else if d == 6 { "6" }
    else if d == 7 { "7" }
    else if d == 8 { "8" }
    else { "9" }
}

/* helper modified by LLM (iteration 4): replaced unsupported push_str with string concatenation */
fn u8_to_string_positive(p: u8) -> (s: String)
    requires p > 0
    ensures s@.len() > 0
{
    if p >= 100 {
        let d1 = p / 100u8;
        let r1 = p % 100u8;
        let d2 = r1 / 10u8;
        let d3 = r1 % 10u8;
        let s_d1 = String::from_str(digit_to_str(d1));
        let s_d12 = s_d1 + digit_to_str(d2);
        s_d12 + digit_to_str(d3)
    } else if p >= 10 {
        let d1 = p / 10u8;
        let d2 = p % 10u8;
        let s_d1 = String::from_str(digit_to_str(d1));
        s_d1 + digit_to_str(d2)
    } else {
        String::from_str(digit_to_str(p))
    }
}

/* helper modified by LLM (iteration 5): fixed mismatched types for string concatenation */
fn i8_to_string(n: i8) -> (s: String)
    ensures
        s@.len() > 0,
        n == 0 ==> s@ == seq!['0'],
        n > 0 ==> forall|i: int| 0 <= i < s@.len() ==> s@[i] != '-',
        n < 0 ==> s@.len() > 1 && s@[0] == '-'
{
    if n == 0 {
        return String::from_str("0");
    }
    
    if n > 0 {
        return u8_to_string_positive(n as u8);
    }

    let p = if n == -128 { 128u8 } else { (-n) as u8 };
    proof {
        assert(p > 0);
    }
    let p_str = u8_to_string_positive(p);
    String::from_str("-") + &p_str
}
// </vc-helpers>

// <vc-spec>
fn array_str(a: Vec<i8>) -> (result: String)
    ensures 
        result@.len() > 0,
        a.len() == 0 ==> result@ == "[]"@,
        a.len() > 0 ==> result@[0] == '[' && result@[(result@.len() - 1) as int] == ']',
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed mismatched types for string concatenation */
    if a.len() == 0 {
        return String::from_str("[]");
    }

    let mut s = String::from_str("[") + &i8_to_string(a[0]);

    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            a.len() > 0,
            s@.len() > 1,
            s@[0] == '[',
        decreases a.len() - i
    {
        s = s + ", ";
        
        let val_str = i8_to_string(a[i]);
        s = s + &val_str;
        
        i = i + 1;
    }

    s = s + "]";
    s
}
// </vc-code>

}
fn main() {}