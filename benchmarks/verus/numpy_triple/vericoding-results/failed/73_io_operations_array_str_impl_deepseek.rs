// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix nat/int usage in ghost code and ensure proper spec syntax */
#[verifier::spec]
fn recursive_stringify(a: Seq<i8>, i: int) -> (s: Seq<char>)
    requires
        i >= 0,
        i <= a.len(),
    ensures
        s.len() == if i == a.len() { 0 } else { 2 + num_digits(a[i] as nat) + recursive_stringify(a, i + 1).len() },
        i < a.len() ==> (s.subrange(0, 1).equal(Seq::new(1, |j: int| if j == 0 { '[' } else { ' ' })) || 
                        s.subrange(0, 1).equal(Seq::new(1, |j: int| if j == 0 { "," } else { ' ' }))),
        i < a.len() ==> s.subrange(s.len() - 1, s.len()).equal(Seq::new(1, |j: int| if j == 0 { ']' } else { ' ' })),
    decreases a.len() - i
{
    if i >= a.len() {
        Seq::empty()
    } else {
        let abs_val = if a[i] < 0 { (-a[i]) as nat } else { a[i] as nat };
        let num_str = digits_to_chars(abs_val);
        let prefix = if i == 0 { seq!['['] } else { seq![',', ' '] };
        let suffix = if i == a.len() - 1 { seq![']'] } else { Seq::empty() };
        prefix + num_str + recursive_stringify(a, i + 1) + suffix
    }
}

#[verifier::spec]
fn num_digits(n: nat) -> (result: nat)
    ensures
        result >= 1,
        n < pow(10, result),
        n >= pow(10, result - 1) || (result == 1 && n == 0),
    decreases n
{
    if n < 10 {
        1
    } else {
        1 + num_digits(n / 10)
    }
}

#[verifier::spec]
fn digits_to_chars(n: nat) -> (s: Seq<char>)
    ensures
        s.len() == num_digits(n),
        forall|i: int| 0 <= i < s.len() ==> s[i].is_ascii_digit(),
    decreases n
{
    if n < 10 {
        Seq::new(1, |i: int| char::from_u8((b'0' + (n as u8)) as u8).unwrap())
    } else {
        digits_to_chars(n / 10) + Seq::new(1, |i: int| char::from_u8((b'0' + ((n % 10) as u8)) as u8).unwrap())
    }
}

#[verifier::spec]
fn pow(base: int, exp: int) -> int
    requires exp >= 0,
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * pow(base, exp - 1)
    }
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
    /* code modified by LLM (iteration 5): Fix compilation errors and implement proper string building */
    let mut result = String::new();
    
    if a.len() == 0 {
        result.push_str("[]");
    } else {
        result.push('[');
        for i in 0..a.len() {
            if i > 0 {
                result.push_str(", ");
            }
            let num = a[i];
            let abs_val = if num < 0 { (-num) as i32 } else { num as i32 };
            result.push_str(&abs_val.to_string());
        }
        result.push(']');
    }
    
    result
}
// </vc-code>

}
fn main() {}