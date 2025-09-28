// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1nat) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

spec fn all_zero(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) + str2int(s2)
{
  assume(false);
  unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor),
    str2int(divisor) > 0
  ensures 
    valid_bit_string(res.0) && valid_bit_string(res.1),
    str2int(res.0) == str2int(dividend) / str2int(divisor),
    str2int(res.1) == str2int(dividend) % str2int(divisor)
{
  assume(false);
  unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) * str2int(s2)
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): fixed all int/nat to usize conversions in executable code */
proof fn lemma_exp_zero(x: nat)
    ensures exp_int(x, 0) == 1
{
}

proof fn lemma_exp_split(x: nat, y: nat)
    requires y > 0
    ensures 
        y % 2 == 0 ==> exp_int(x, y) == exp_int(x * x, y / 2),
        y % 2 == 1 ==> exp_int(x, y) == x * exp_int(x * x, y / 2)
    decreases y
{
    if y == 1 {
        assert(exp_int(x, 1) == x * exp_int(x, 0));
        assert(exp_int(x, 0) == 1);
    } else if y % 2 == 0 {
        assert(exp_int(x, y) == x * exp_int(x, (y - 1) as nat));
        lemma_exp_split(x, (y - 1) as nat);
    } else {
        assert(exp_int(x, y) == x * exp_int(x, (y - 1) as nat));
        lemma_exp_split(x, (y - 1) as nat);
    }
}

spec fn is_zero_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn is_zero(s: &Seq<char>) -> (b: bool)
    requires valid_bit_string(*s)
    ensures b == (str2int(*s) == 0)
{
    let mut i: usize = 0;
    let len = s.len() as usize;
    while i < len
        invariant
            0 <= i <= len,
            len == s.len() as usize,
            forall|j: int| 0 <= j < i as int ==> (#[trigger] (*s)[j]) == '0'
    {
        if (*s)[i as int] != '0' {
            return false;
        }
        i = i + 1;
    }
    true
}

fn div_by_2(s: &Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(*s),
        s.len() > 0
    ensures 
        valid_bit_string(res),
        str2int(res) == str2int(*s) / 2
{
    if s.len() == 1 {
        seq!['0']
    } else {
        s.subrange(0, s.len() - 1)
    }
}

fn is_odd(s: &Seq<char>) -> (b: bool)
    requires 
        valid_bit_string(*s),
        s.len() > 0
    ensures b == (str2int(*s) % 2 == 1)
{
    (*s)[s.len() - 1] == '1'
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
    /* code modified by LLM (iteration 10): fixed nat type comparison to use usize */
    if sy.len() == 0 || is_zero(&sy) {
        proof {
            lemma_exp_zero(str2int(sx));
        }
        let one = seq!['1'];
        let res = div_mod(one, sz).1;
        return res;
    }
    
    let half_y = div_by_2(&sy);
    let half_power = mod_exp(sx, half_y, sz);
    let squared = mul(half_power, half_power);
    let squared_mod = div_mod(squared, sz).1;
    
    if is_odd(&sy) {
        proof {
            lemma_exp_split(str2int(sx), str2int(sy));
        }
        let result = mul(squared_mod, sx);
        let final_mod = div_mod(result, sz).1;
        final_mod
    } else {
        proof {
            lemma_exp_split(str2int(sx), str2int(sy));
        }
        squared_mod
    }
}
// </vc-code>


}

fn main() {}