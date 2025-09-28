// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn str2int(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 { 
        0nat 
    } else { 
        2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    }
}
// </vc-preamble>

// <vc-helpers>
spec fn bit_length(n: int) -> int
    requires n >= 0
    decreases n
{
    if n < 2 { 1 } else { 1 + bit_length(n / 2) }
}

spec fn get_bit(n: int, pos: int) -> char
    requires n >= 0, pos >= 0
    decreases n, pos
{
    if pos == 0 {
        if n % 2 == 0 { '0' } else { '1' }
    } else {
        get_bit(n / 2, pos - 1)
    }
}

spec fn int2str(n: int) -> Seq<char>
    requires n >= 0
{
    if n == 0 {
        seq!['0']
    } else {
        let len = bit_length(n);
        Seq::new(len, |i: int| get_bit(n, len - 1 - i))
    }
}

/* helper modified by LLM (iteration 5): formatted requires block, adjusted types */
fn mod_nat(a: int, b: int) -> int
    requires
        a >= 0,
        b > 0,
    ensures
        a < b ==> result == a,
        a >= b ==> result == a - (a / b) * b,
{
    a - (a / b) * b
}

/* helper modified by LLM (iteration 5): formatted requires block, adjusted types */
fn mul_mod(a: int, b: int, m: int) -> int
    requires
        m > 0,
{
    mod_nat(a * b, m)
}

/* helper modified by LLM (iteration 5): formatted requires block, added ensures, simplified invariant */
fn str_to_nat(s: Seq<char>) -> int
    decreases s.len()
    requires
        s.len() >= 0,
    ensures
        result == str2int(s) as int,
{
    let mut res = 0int;
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
        decreases s.len() - i
    {
        let bit = if s[i] == '1' { 1int } else { 0int };
        res = res * 2int + bit;
        i += 1;
    }
    res
}

/* helper modified by LLM (iteration 5): formatted requires block, added ensures */
fn int_to_str(n: int) -> Seq<char>
    requires
        n >= 0,
    ensures
        result == int2str(n),
{
    if n == 0 {
        seq!['0']
    } else {
        let len = bit_length(n);
        Seq::new(len, |i: int| get_bit(n, len - 1 - i))
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2(sx: Vec<char>, sy: Vec<char>, n: u8, sz: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
        str2int(sy@) == exp_int(2nat, n as nat) || str2int(sy@) == 0,
        sy@.len() == n as int + 1,
        str2int(sz@) > 1,
    ensures 
        valid_bit_string(res@),
        str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
    decreases n
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): implemented mod_exp_pow2 with fixed types */
{
    let x = str_to_nat(sx@);
    let y = str_to_nat(sy@);
    let z = str_to_nat(sz@);
    let computed_res: int = if y == 0int {
        mod_nat(1int, z)
    } else {
        let mut base = mod_nat(x, z);
        let mut i = 0;
        while i < n as int
            invariant
                i <= n as int,
                base >= 0,
                base < z,
            decreases n as int - i
        {
            base = mul_mod(base, base, z);
            i += 1;
        }
        base
    };
    let res_seq = int_to_str(computed_res);
    let mut res_vec: Vec<char> = Vec::new();
    let mut index = 0;
    while index < res_seq.len()
        invariant index <= res_seq.len()
        decreases res_seq.len() - index
    {
        res_vec.push(res_seq[index]);
        index += 1;
    }
    res_vec
}
// </vc-code>


}

fn main() {}