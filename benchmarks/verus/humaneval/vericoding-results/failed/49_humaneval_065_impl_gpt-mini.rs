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
/* helper modified by LLM (iteration 3): absolute value helper for i8 */
spec fn abs_i8(x: i8) -> int
{
    if (x as int) < 0 { -((x as int)) } else { x as int }
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
    /* code modified by LLM (iteration 3): compute digits and perform circular shift without using spec sequences or 'int' in executable code */
    // compute absolute value as i32
    let mut n_val: i32 = x as i32;
    if n_val < 0 { n_val = -n_val; }

    // build digits in reverse order (least-significant first)
    let mut rev: Vec<char> = Vec::new();
    if n_val == 0 {
        rev.push('0');
    } else {
        let mut tmp: i32 = n_val;
        while tmp > 0
            invariant
                tmp >= 0,
            decreases
                tmp
        {
            let d: u8 = (tmp % 10) as u8;
            rev.push((('0' as u8) + d) as char);
            tmp = tmp / 10;
        }
    }

    // reverse into correct order
    let mut digits: Vec<char> = Vec::new();
    let rev_len = rev.len();
    let mut r_idx: usize = 0;
    while r_idx < rev_len
        invariant
            r_idx <= rev_len,
        decreases
            rev_len - r_idx
    {
        digits.push(rev[rev_len - 1 - r_idx]);
        r_idx += 1;
    }

    // length and shift as native integers
    let len_usize: usize = digits.len();
    if len_usize == 0 {
        return digits;
    }
    let len_i32: i32 = len_usize as i32;
    let shift_i32: i32 = shift as i32;

    // if shift greater than length -> return reversed digits
    if shift_i32 > len_i32 {
        let mut res_rev: Vec<char> = Vec::new();
        let mut k: usize = 0;
        while k < len_usize
            invariant
                k <= len_usize,
            decreases
                len_usize - k
        {
            res_rev.push(digits[len_usize - 1 - k]);
            k += 1;
        }
        return res_rev;
    }

    // normalize shift (handle negative modulo safely)
    let mut normalized: i32 = shift_i32 % len_i32;
    if normalized < 0 { normalized += len_i32; }
    if normalized == 0 {
        return digits;
    }

    let start: usize = (len_i32 - normalized) as usize;
    let mut res: Vec<char> = Vec::new();

    // push from start to end
    let mut p: usize = start;
    while p < len_usize
        invariant
            start <= p,
            p <= len_usize,
        decreases
            len_usize - p
    {
        res.push(digits[p]);
        p += 1;
    }

    // push from 0 to start
    let mut q: usize = 0;
    while q < start
        invariant
            0 <= q,
            q <= start,
        decreases
            start - q
    {
        res.push(digits[q]);
        q += 1;
    }

    res
}
// </vc-code>


}

fn main() {}