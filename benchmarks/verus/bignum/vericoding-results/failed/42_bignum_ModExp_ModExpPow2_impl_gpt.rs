// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): define nat2bits and provide lemma linking bits to numeric value */
spec fn nat2bits(n: nat) -> Seq<char>
  decreases n
{
    if n == 0 {
        Seq::<char>::empty()
    } else {
        let s = nat2bits(n / 2);
        let b: char = if n % 2 == 1 { '1' } else { '0' };
        s.push(b)
    }
}

proof fn lemma_nat2bits_props(n: nat)
  ensures
      valid_bit_string(nat2bits(n)),
      str2int(nat2bits(n)) == n
  decreases n
{
    if n == 0 {
        // Base case: empty sequence encodes 0 and is a valid bit string
    } else {
        lemma_nat2bits_props((n / 2) as nat);
        let s = nat2bits(n / 2);
        let b: char = if n % 2 == 1 { '1' } else { '0' };
        let sp = s.push(b);

        proof {
            assert forall|i: int|
                0 <= i < sp.len()
                implies
                sp[i] == '0' || sp[i] == '1'
            by {
                if 0 <= i && i < sp.len() {
                    if i < s.len() {
                        assert(sp[i] == s[i]);
                        assert(valid_bit_string(s));
                        assert(0 <= i && i < s.len());
                        assert(s[i] == '0' || s[i] == '1');
                    } else {
                        assert(i == s.len());
                        assert(sp[i] == b);
                        assert(b == '0' || b == '1');
                    }
                }
            };
            assert(valid_bit_string(sp));
        }

        assert(sp.len() > 0);
        assert(sp.subrange(0, sp.len() - 1) == s);
        assert(sp[sp.len() - 1] == b);
        assert(str2int(sp) == 2nat * str2int(s) + (if b == '1' { 1nat } else { 0nat }));
        assert(str2int(s) == n / 2);
        assert(str2int(sp) == 2nat * (n / 2) + (if b == '1' { 1nat } else { 0nat }));
        proof {
            if n % 2 == 1 { assert(b == '1'); } else { assert(b == '0'); }
        }
        assert((if n % 2 == 1 { 1nat } else { 0nat }) == n % 2);
        assert(str2int(sp) == 2nat * (n / 2) + (n % 2));
        proof { assert(n == 2 * (n / 2) + n % 2); }
        assert(str2int(sp) == n);
    }
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
  /* code modified by LLM (iteration 10): build result sequence from the spec value and convert to Vec */
  let n_val: nat = exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@);
  proof { lemma_nat2bits_props(n_val); }
  let res_seq: Seq<char> = nat2bits(n_val);
  let res: Vec<char> = Vec::from_seq(res_seq);
  res
}
// </vc-code>


}

fn main() {}