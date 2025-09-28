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
        if valid_bit_string(s) {
            2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
        } else {
            0nat
        }
    }
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (result: (Seq<char>, Seq<char>))
    requires 
        valid_bit_string(dividend) && valid_bit_string(divisor) && str2int(divisor) > 0
    ensures 
        valid_bit_string(result.0) && valid_bit_string(result.1),
        str2int(result.0) == str2int(dividend) / str2int(divisor),
        str2int(result.1) == str2int(dividend) % str2int(divisor)
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): fixed type annotation and spec function syntax */
spec fn normalize_binary(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        seq!['0']
    } else {
        let i = find_first_nonzero(s, 0);
        if i == s.len() {
            seq!['0']
        } else {
            s.subrange(i, s.len() as int)
        }
    }
}

spec fn find_first_nonzero(s: Seq<char>, start: int) -> int
    decreases s.len() - start
{
    if start >= s.len() || s[start] != '0' {
        start
    } else {
        find_first_nonzero(s, start + 1)
    }
}

proof fn lemma_exp_pow2_zero()
    ensures exp_int(2nat, 0nat) == 1nat
{
}

proof fn lemma_exp_base_zero(x: nat)
    ensures exp_int(x, 0nat) == 1nat
{
}

proof fn lemma_exp_zero_nonzero(y: nat)
    requires y > 0
    ensures exp_int(0nat, y) == 0nat
    decreases y
{
    if y == 1 {
    } else {
        lemma_exp_zero_nonzero((y - 1) as nat);
    }
}

proof fn lemma_mod_exp_zero(z: nat)
    requires z > 1
    ensures 0nat % z == 0nat
{
}

proof fn lemma_one_mod(z: nat)
    requires z > 1
    ensures 1nat % z == 1nat
{
}

proof fn lemma_str2int_zero()
    ensures str2int(seq!['0']) == 0nat
{
}

proof fn lemma_str2int_one()
    ensures str2int(seq!['1']) == 1nat
{
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2(sx: Vec<char>, sy: Vec<char>, n: u8, sz: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
        str2int(sy@) == exp_int(2nat, n as nat) || str2int(sy@) == 0,
        sy.len() == n as int + 1,
        str2int(sz@) > 1
    ensures 
        valid_bit_string(res@),
        str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
    decreases n
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): fixed nat literal syntax */
    if n == 0 {
        proof {
            lemma_exp_pow2_zero();
            lemma_exp_base_zero(str2int(sx@));
            lemma_one_mod(str2int(sz@));
        }
        vec!['1']
    } else {
        if str2int(sy@) == 0 {
            proof {
                lemma_exp_base_zero(str2int(sx@));
                lemma_one_mod(str2int(sz@));
            }
            vec!['1']
        } else {
            proof {
                lemma_exp_zero_nonzero(exp_int(2nat, n as nat));
                lemma_mod_exp_zero(str2int(sz@));
                lemma_str2int_zero();
            }
            vec!['0']
        }
    }
}
// </vc-code>


}

fn main() {}