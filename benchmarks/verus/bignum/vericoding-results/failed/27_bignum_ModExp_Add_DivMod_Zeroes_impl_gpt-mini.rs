// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2_int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    if valid_bit_string(s) {
      2 * str2_int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    } else {
      0nat
    }
  }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn all_zero(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2_int(res) == str2_int(s1) + str2_int(s2),
{
  assume(false);
  unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (quotient_remainder: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor) &&
    str2_int(divisor) > 0,
  ensures 
    valid_bit_string(quotient_remainder.0) && valid_bit_string(quotient_remainder.1) &&
    str2_int(quotient_remainder.0) == str2_int(dividend) / str2_int(divisor) &&
    str2_int(quotient_remainder.1) == str2_int(dividend) % str2_int(divisor),
{
  assume(false);
  unreached()
}

fn zeros(n: nat) -> (s: Seq<char>)
  ensures 
    s.len() == n &&
    valid_bit_string(s) &&
    str2_int(s) == 0 &&
    all_zero(s),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): fixed Seq construction and indexing (use Seq::from and direct Seq indexing) */
fn nat_to_bits(mut n0: u64) -> (res: Seq<char>)
  ensures
    valid_bit_string(res) && str2_int(res) == (n0 as nat)
{
    let mut n = n0;
    let mut v = std::vec::Vec::<char>::new();
    if n == 0u64 {
        v.push('0');
    } else {
        let mut digits = std::vec::Vec::<char>::new();
        while n > 0u64
            invariant
                // digits length is non-decreasing
                digits.len() >= 0,
            decreases n
        {
            if n % 2u64 == 1u64 { digits.push('1'); } else { digits.push('0'); }
            n = n / 2u64;
        }
        let mut i: usize = 0usize;
        while i < digits.len()
            invariant
                i <= digits.len(),
            decreases digits.len() - i
        {
            let idx = digits.len() - 1 - i;
            let c = digits[idx];
            v.push(c);
            i = i + 1usize;
        }
    }
    let s = Seq::from(v);
    proof {
        assert(forall|j: int| 0 <= j < s.len() ==> (s[j] == '0' || s[j] == '1'));
        if n0 == 0u64 {
            assert(s.len() == 1);
            assert(s[0] == '0');
            assert(str2_int(s) == 0nat);
        } else {
            let mut acc: nat = 0nat;
            let mut k: int = 0;
            while k < s.len()
                invariant
                    0 <= k <= s.len(),
                decreases s.len() - k
            {
                let b = s[s.len() - 1 - k];
                if b == '1' {
                    acc = acc + exp_int(2nat, (k as nat));
                }
                k = k + 1;
            }
            assert(acc == (n0 as nat));
            assert(str2_int(s) == (n0 as nat));
        }
    }
    s
}

/* helper modified by LLM (iteration 10): convert Seq to u64 using direct Seq indexing */
fn seq_to_u64(s: Seq<char>) -> (res: u64)
  requires
    valid_bit_string(s),
  ensures
    str2_int(s) == (res as nat)
{
    let mut acc: u64 = 0u64;
    let mut i: int = 0;
    while i < s.len()
        invariant
            0 <= i && i <= s.len(),
        decreases s.len() - i
    {
        let c = s[i];
        acc = acc * 2u64 + (if c == '1' { 1u64 } else { 0u64 });
        i = i + 1;
    }
    proof {
        assert(str2_int(s) == (acc as nat));
    }
    acc
}

// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz) &&
    sy.len() > 0 && str2_int(sz) > 1,
  ensures 
    valid_bit_string(res) &&
    str2_int(res) == exp_int(str2_int(sx), str2_int(sy)) % str2_int(sz),
  decreases sy.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): perform modular exponentiation using helper conversions and direct Seq indexing */
{
    let modulus = seq_to_u64(sz);
    let base0 = seq_to_u64(sx);
    let exp0 = seq_to_u64(sy);
    let mut base = base0 % modulus;
    let mut exp = exp0;
    let mut result_num = 1u64 % modulus;
    while exp > 0u64
        invariant
            result_num < modulus,
        decreases
            exp
    {
        if exp % 2u64 == 1u64 {
            result_num = (result_num * base) % modulus;
        }
        base = (base * base) % modulus;
        exp = exp / 2u64;
    }
    let res = nat_to_bits(result_num);
    proof {
        assert(valid_bit_string(res));
        assert(str2_int(res) == (result_num as nat));
    }
    res
}

// </vc-code>


}

fn main() {}