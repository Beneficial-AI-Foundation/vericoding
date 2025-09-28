// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
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
  if y == 0 {
    1nat
  } else {
    x * exp_int(x, (y - 1) as nat)
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
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
/* helper modified by LLM (iteration 10): added proper modular arithmetic lemma */
proof fn lemma_str2int_zeros(n: nat)
    ensures forall|s: Seq<char>| s.len() == n && all_zero(s) ==> str2int(s) == 0
    decreases n
{
    if n == 0 {
        // Base case: empty sequence
        assert(forall|s: Seq<char>| s.len() == 0 ==> str2int(s) == 0);
    } else {
        // Inductive case
        lemma_str2int_zeros((n-1) as nat);
        assert(forall|s: Seq<char>| s.len() == n && all_zero(s) ==> {
            let prefix = s.subrange(0, s.len() - 1);
            all_zero(prefix) && prefix.len() == (n-1) as nat &&
            s[s.len() - 1] == '0' &&
            str2int(s) == 2nat * str2int(prefix) + 0nat &&
            str2int(prefix) == 0nat &&
            str2int(s) == 0nat
        });
    }
}

proof fn lemma_exp_zero(base: nat)
    ensures exp_int(base, 0nat) == 1nat
{
    // Follows directly from definition
}

proof fn lemma_mod_arith(m: nat)
    requires m > 1nat
    ensures 1nat % m == 1nat
{
    // Mathematical fact: for any m > 1, 1 % m = 1
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
    sy.len() > 0 && str2int(sz@) > 1
  ensures 
    valid_bit_string(res@),
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): handle all zero case and fix recursion */
    
    // Check if sy represents 0
    let mut is_zero = true;
    for i in 0..sy.len()
        invariant
            is_zero == forall|j: int| 0 <= j < i ==> sy[j] == '0'
    {
        if sy[i] == '1' {
            is_zero = false;
            break;
        }
    }
    
    if is_zero {
        let ones = vec!['1'];
        proof {
            lemma_exp_zero(str2int(sx@));
            assert(all_zero(sy@));
            lemma_str2int_zeros(sy.len() as nat);
            assert(str2int(sy@) == 0nat);
            assert(exp_int(str2int(sx@), 0nat) == 1nat);
            assert(str2int(ones@) == 1nat);
            lemma_mod_arith(str2int(sz@));
        }
        return ones;
    }
    
    if sy.len() == 1 {
        proof {
            assert(sy[0] == '1');
            assert(str2int(sy@) == 1nat);
            assert(exp_int(str2int(sx@), 1nat) == str2int(sx@));
        }
        return sx;
    }
    
    let mut sy_tail = Vec::new();
    for i in 1..sy.len()
        invariant
            sy_tail.len() == i - 1,
            forall|j: int| 0 <= j < sy_tail.len() ==> sy_tail[j] == sy[j + 1],
            valid_bit_string(sy_tail@)
    {
        sy_tail.push(sy[i]);
    }
    
    proof {
        assert(sy_tail.len() > 0);
        assert(sy_tail.len() < sy.len());
        assert(valid_bit_string(sy_tail@));
        assert(str2int(sz@) > 1);
    }
    
    return mod_exp(sx, sy_tail, sz);
}
// </vc-code>


}

fn main() {}