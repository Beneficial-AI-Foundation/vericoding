// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    2nat * str2int(s.subrange(0, s.len() - 1)) + 
    (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn all_zero(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (result: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor),
    str2int(divisor) > 0,
  ensures 
    valid_bit_string(result.0) && valid_bit_string(result.1),
    str2int(result.0) == str2int(dividend) / str2int(divisor),
    str2int(result.1) == str2int(dividend) % str2int(divisor),
{
  assume(false);
  unreached()
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0,
    sy.len() == n + 1,
    str2int(sz) > 1,
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz),
  decreases n
{
  assume(false);
  unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) * str2int(s2),
{
  assume(false);
  unreached()
}

fn zeros(n: nat) -> (s: Seq<char>)
  ensures 
    s.len() == n,
    valid_bit_string(s),
    str2int(s) == 0,
    all_zero(s),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added helper functions for modular exponentiation */
proof fn lemma_exp_int_mod(x: nat, y: nat, m: nat)
    requires m > 1
    ensures exp_int(x, y) % m == exp_int(x % m, y) % m
{
    if y == 0 {
        assert(exp_int(x, 0) % m == 1 % m);
        assert(exp_int(x % m, 0) % m == 1 % m);
    } else {
        lemma_exp_int_mod(x, y - 1, m);
        assert(exp_int(x, y) == x * exp_int(x, y - 1));
        assert(exp_int(x % m, y) == (x % m) * exp_int(x % m, y - 1));
        assert((x * exp_int(x, y - 1)) % m == ((x % m) * exp_int(x % m, y - 1)) % m);
    }
}

spec fn is_power_of_two(n: nat) -> bool {
    n > 0 && (n & (n - 1)) == 0
}

spec fn log2(n: nat) -> nat
    decreases n
    requires is_power_of_two(n)
{
    if n == 1 { 0nat } else { log2(n / 2) + 1nat }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    sy.len() > 0 && str2int(sz) > 1,
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz),
  decreases sy.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implemented modular exponentiation algorithm */
    if sy.len() == 1 && sy[0] == '0' {
        zeros(1)
    } else {
        let n = sy.len() - 1;
        if is_power_of_two(str2int(sy)) {
            mod_exp_pow2(sx, sy, n, sz)
        } else {
            let (quotient, remainder) = div_mod(sy, seq!['1'])
            let half_result = mod_exp(sx, quotient, sz);
            let square_result = mul(half_result, half_result);
            if remainder[0] == '0' {
                square_result
            } else {
                let temp = mul(square_result, sx);
                div_mod(temp, sz).1
            }
        }
    }
}
// </vc-code>


}

fn main() {}