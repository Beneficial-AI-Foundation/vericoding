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
/* helper modified by LLM (iteration 5): Fixed helper functions for correct verification */
spec fn digit_to_char(d: int) -> char
    recommends 0 <= d <= 9
{
    ((d + ('0' as int)) as char)
}

fn int_to_vec(x: i8) -> (result: Vec<char>)
    requires x >= 0
    ensures result@ == int_to_string(x as int),
            forall|i: int| 0 <= i < result.len() ==> '0' <= result[i] && result[i] <= '9'
{
    if x == 0 {
        let mut v = Vec::new();
        v.push('0');
        proof {
            assert(v@ == seq!['0']);
            assert(int_to_string(0) == seq!['0']);
        }
        v
    } else {
        int_to_vec_helper(x, Vec::new())
    }
}

fn int_to_vec_helper(x: i8, mut acc: Vec<char>) -> (result: Vec<char>)
    requires x >= 0,
             forall|i: int| 0 <= i < acc.len() ==> '0' <= acc[i] && acc[i] <= '9'
    ensures result@ == int_to_string_helper(x as int, acc@),
            forall|i: int| 0 <= i < result.len() ==> '0' <= result[i] && result[i] <= '9'
    decreases x
{
    if x == 0 {
        acc
    } else {
        let digit = (x % 10) as u8;
        let digit_char = (digit + ('0' as u8)) as char;
        acc.insert(0, digit_char);
        proof {
            assert(0 <= digit && digit <= 9);
            assert('0' <= digit_char && digit_char <= '9');
        }
        int_to_vec_helper(x / 10, acc)
    }
}

fn reverse_vec(v: &Vec<char>) -> (result: Vec<char>)
    ensures result.len() == v.len(),
            result@ == reverse_string(v@),
            forall|i: int| 0 <= i < v.len() ==> v[i] == result[v.len() - 1 - i]
{
    let n = v.len();
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == v[n - 1 - j],
        decreases n - i
    {
        result.push(v[n - 1 - i]);
        i = i + 1;
    }
    result
}

fn circular_shift_vec(v: &Vec<char>, shift: usize) -> (result: Vec<char>)
    requires v.len() > 0,
             shift < v.len(),
             forall|i: int| 0 <= i < v.len() ==> '0' <= v[i] && v[i] <= '9'
    ensures result.len() == v.len(),
            shift == 0 ==> result@ == v@,
            shift > 0 ==> {
                let n = v.len() as int;
                result@ == v@.subrange(n - (shift as int), n).add(v@.subrange(0, n - (shift as int)))
            },
            forall|i: int| 0 <= i < result.len() ==> '0' <= result[i] && result[i] <= '9'
{
    let n = v.len();
    let mut result = Vec::new();
    
    if shift == 0 {
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                result.len() == i,
                result@ == v@.subrange(0, i as int),
                forall|j: int| 0 <= j < i ==> '0' <= result[j] && result[j] <= '9',
            decreases n - i
        {
            result.push(v[i]);
            i = i + 1;
        }
    } else {
        let mut i: usize = n - shift;
        while i < n
            invariant
                n - shift <= i && i <= n,
                result.len() == i - (n - shift),
                n >= shift,
                result@ == v@.subrange((n - shift) as int, i as int),
                forall|j: int| 0 <= j < result.len() ==> '0' <= result[j] && result[j] <= '9',
            decreases n - i
        {
            result.push(v[i]);
            i = i + 1;
        }
        
        let mut j: usize = 0;
        while j < n - shift
            invariant
                j <= n - shift,
                result.len() == shift + j,
                n >= shift,
                result@ == v@.subrange((n - shift) as int, n as int).add(v@.subrange(0, j as int)),
                forall|k: int| 0 <= k < result.len() ==> '0' <= result[k] && result[k] <= '9',
            decreases n - shift - j
        {
            result.push(v[j]);
            j = j + 1;
        }
    }
    result
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
    /* code modified by LLM (iteration 5): Fixed arithmetic overflow and type casting issues */
    let abs_x: i8 = if x == i8::MIN { 
        // Special case to avoid overflow
        let mut digits = int_to_vec(12);
        digits[0] = '1';
        digits[1] = '2';
        digits.push('8');
        if shift > 3 {
            return reverse_vec(&digits);
        } else if shift <= 0 {
            return digits;
        } else {
            let normalized_shift = (shift as usize) % 3;
            if normalized_shift == 0 {
                return digits;
            } else {
                return circular_shift_vec(&digits, normalized_shift);
            }
        }
    } else if x < 0 { 
        (0 - x) 
    } else { 
        x 
    };
    
    let mut digits = int_to_vec(abs_x);
    
    proof {
        assert(digits@ == int_to_string(abs_x as int));
        assert(forall|i: int| 0 <= i < digits.len() ==> '0' <= digits[i] && digits[i] <= '9');
    }
    
    if digits.len() == 0 {
        digits
    } else if shift <= 0 {
        digits
    } else if shift >= digits.len() as i8 {
        reverse_vec(&digits)
    } else {
        let normalized_shift = (shift as usize) % digits.len();
        if normalized_shift == 0 {
            digits
        } else if normalized_shift < digits.len() {
            circular_shift_vec(&digits, normalized_shift)
        } else {
            digits
        }
    }
}
// </vc-code>


}

fn main() {}