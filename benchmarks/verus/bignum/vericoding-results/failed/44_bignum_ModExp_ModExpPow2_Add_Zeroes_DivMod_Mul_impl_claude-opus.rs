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
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
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

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0,
    sy.len() == n + 1,
    str2int(sz) > 1
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases n
{
  assume(false);
  unreached()
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) + str2int(s2)
{
  assume(false);
  unreached()
}

fn zeros(n: nat) -> (s: Seq<char>)
  ensures 
    s.len() == n,
    valid_bit_string(s),
    str2int(s) == 0,
    all_zero(s)
{
  assume(false);
  unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (ret: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor),
    str2int(divisor) > 0
  ensures 
    valid_bit_string(ret.0) && valid_bit_string(ret.1),
    str2int(ret.0) == str2int(dividend) / str2int(divisor),
    str2int(ret.1) == str2int(dividend) % str2int(divisor)
{
  assume(false);
  unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) * str2int(s2)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed spec function to use int parameter instead of nat */
spec fn seq_at(s: Seq<char>, i: int) -> char
    recommends 0 <= i < s.len()
{
    s[i]
}

proof fn lemma_exp_split(x: nat, y: nat, z: nat)
    requires z > 1, y > 0
    ensures 
        y % 2 == 0 ==> exp_int(x, y) % z == (exp_int(x, y/2) * exp_int(x, y/2)) % z,
        y % 2 == 1 ==> exp_int(x, y) % z == (x * exp_int(x, (y-1) as nat)) % z
    decreases y
{
    if y % 2 == 0 {
        assert(exp_int(x, y) == exp_int(x, y/2) * exp_int(x, y/2)) by {
            reveal(exp_int);
            if y == 2 {
                assert(exp_int(x, 2) == x * exp_int(x, 1));
                assert(exp_int(x, 1) == x * exp_int(x, 0));
                assert(exp_int(x, 0) == 1);
                assert(exp_int(x, 2) == x * x);
                assert(exp_int(x, 1) == x);
                assert(exp_int(x, y/2) == x);
            } else if y > 2 {
                lemma_exp_split(x, y/2, z);
            }
        }
    } else {
        assert(exp_int(x, y) == x * exp_int(x, (y-1) as nat)) by {
            reveal(exp_int);
        }
    }
}

proof fn lemma_str2int_zeros(n: nat)
    ensures str2int(zeros(n)) == 0
{
    let s = zeros(n);
    assert(all_zero(s));
    assert(forall|i: int| 0 <= i < s.len() ==> s[i] == '0');
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    sy.len() > 0 && str2int(sz) > 1
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases sy.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fixed nat usage - removed as nat cast for zeros parameter */
    if sy.len() == 1 && seq_at(sy, 0) == '0' {
        // y = 0, so x^0 = 1
        let one = seq!['1'];
        proof {
            assert(str2int(sy) == 0) by {
                reveal(str2int);
                assert(sy.subrange(0, 0).len() == 0);
            }
            assert(exp_int(str2int(sx), 0) == 1) by {
                reveal(exp_int);
            }
        }
        let (_, remainder) = div_mod(one, sz);
        remainder
    } else if all_zero(sy) {
        // y = 0, so x^0 = 1
        let one = seq!['1'];
        proof {
            lemma_str2int_zeros(sy.len() as nat);
            assert(str2int(sy) == 0);
            assert(exp_int(str2int(sx), 0) == 1) by {
                reveal(exp_int);
            }
        }
        let (_, remainder) = div_mod(one, sz);
        remainder
    } else if seq_at(sy, sy.len() - 1) == '0' {
        // y is even
        let (half_y, _) = div_mod(sy, seq!['1', '0']);
        let rec_result = mod_exp(sx, half_y, sz);
        let squared = mul(rec_result, rec_result);
        let (_, remainder) = div_mod(squared, sz);
        proof {
            assert(str2int(seq!['1', '0']) == 2);
            lemma_exp_split(str2int(sx), str2int(sy), str2int(sz));
        }
        remainder
    } else {
        // y is odd
        let one = seq!['1'];
        let y_minus_1 = if sy.len() == 1 {
            zeros(1)
        } else {
            let (quotient, _) = div_mod(sy, seq!['1', '0']);
            let doubled = mul(quotient, seq!['1', '0']);
            doubled
        };
        
        let rec_result = mod_exp(sx, y_minus_1, sz);
        let product = mul(sx, rec_result);
        let (_, remainder) = div_mod(product, sz);
        proof {
            lemma_exp_split(str2int(sx), str2int(sy), str2int(sz));
        }
        remainder
    }
}
// </vc-code>


}

fn main() {}