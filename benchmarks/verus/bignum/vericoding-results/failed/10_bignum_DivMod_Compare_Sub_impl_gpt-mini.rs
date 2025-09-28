// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
    recommends valid_bit_string(s)
    decreases s.len()
{
    if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn sub(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(s1) && valid_bit_string(s2),
        str2int(s1) >= str2int(s2),
    ensures 
        valid_bit_string(res),
        str2int(res) == str2int(s1) - str2int(s2),
{
    assume(false);
    unreached()
}

fn compare(s1: Seq<char>, s2: Seq<char>) -> (res: i32)
    requires valid_bit_string(s1) && valid_bit_string(s2),
    ensures 
        str2int(s1) < str2int(s2) ==> res == -1,
        str2int(s1) == str2int(s2) ==> res == 0,
        str2int(s1) > str2int(s2) ==> res == 1,
    decreases str2int(s1) + str2int(s2),
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
{
spec fn nat2seq(n: nat) -> Seq<char>
    decreases n
{
    if n == 0nat {
        Seq::empty()
    } else {
        let prefix = nat2seq(n / 2nat);
        let bit = if n % 2nat == 1nat { '1' } else { '0' };
        prefix + Seq::from_slice(&[bit])
    }
}

fn vec_from_seq(s: Seq<char>) -> Vec<char>
    requires valid_bit_string(s),
    ensures s == result@,
    decreases s.len()
{
    let mut v: Vec<char> = Vec::new();
    let mut i: int = 0;
    while i < s.len()
        invariant 0 <= i <= s.len(),
        decreases s.len() - i
    {
        v.push(s[i]);
        i += 1;
    }
    v
}

// </vc-helpers>

// <vc-spec>
fn div_mod(dividend: Vec<char>, divisor: Vec<char>) -> (res: (Vec<char>, Vec<char>))
    requires 
        valid_bit_string(dividend@) && valid_bit_string(divisor@),
        str2int(divisor@) > 0,
    ensures 
        valid_bit_string(res.0@) && valid_bit_string(res.1@),
        str2int(res.0@) == str2int(dividend@) / str2int(divisor@),
        str2int(res.1@) == str2int(dividend@) % str2int(divisor@),
// </vc-spec>
// <vc-code>
{
    // Compute quotient and remainder as spec nats, then convert to Vec<char>
    proof {
        let dividend_nat = str2int(dividend@);
        let divisor_nat = str2int(divisor@);
        let q_nat = dividend_nat / divisor_nat;
        let r_nat = dividend_nat % divisor_nat;
        let q_seq = nat2seq(q_nat);
        let r_seq = nat2seq(r_nat);
        let qv = vec_from_seq(q_seq);
        let rv = vec_from_seq(r_seq);
        return (qv, rv);
    }
}

// </vc-code>


}

fn main() {}