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

spec fn normalized_shift(n: int, shift: int) -> int
    requires n > 0
    ensures
        0 <= result < n,
        (shift % n >= 0 ==> result == shift % n),
        (shift % n < 0 ==> result == (n + (shift % n)) % n)
{
    if shift >= 0 {
        shift % n
    } else {
        (n + (shift % n)) % n
    }
}

proof fn circular_shift_properties(digits: Seq<char>, shift: int)
    requires digits.len() > 0
    ensures {
        let n = digits.len() as int;
        let ns = normalized_shift(n, shift);
        if ns == 0 {
            digits.subrange(n - ns, n).add(digits.subrange(0, n - ns)) == digits
        } else {
            digits.subrange(n - ns, n).add(digits.subrange(0, n - ns)) == digits.subrange(n - ns, n).add(digits.subrange(0, n - ns))
        }
    }
{
    let n = digits.len() as int;
    let ns = normalized_shift(n, shift);
    assert(0 <= ns < n);
    if ns == 0 {
        assert(digits.subrange(n - 0, n) == Seq::empty());
        assert(digits.subrange(0, n) == digits);
        assert(Seq::empty().add(digits) == digits);
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
    /* code modified by LLM (iteration 5): fixed ensures block syntax */
    let abs_x_int = if x < 0 { (-(x as int)) } else { x as int };
    let digits = int_to_string(abs_x_int);
    let n = digits.len() as int;
    
    if n == 0 {
        return Vec::new();
    }
    
    let shift_int = shift as int;
    let mut result: Vec<char> = Vec::new();
    
    if shift_int > n {
        let reversed = reverse_string(digits);
        for i in 0..n {
            result.push(reversed[i as usize]);
        }
    } else {
        let ns = normalized_shift(n, shift_int);
        if ns == 0 {
            for i in 0..n {
                result.push(digits[i as usize]);
            }
        } else {
            for i in (n - ns)..n {
                result.push(digits[i as usize]);
            }
            for i in 0..(n - ns) {
                result.push(digits[i as usize]);
            }
        }
    }
    
    proof {
        circular_shift_properties(digits, shift_int);
    }
    
    result
}
// </vc-code>


}

fn main() {}