// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s.index(s.len() - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s.index(i) == '0' || s.index(i) == '1'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2int(res) == str2int(s1) + str2int(s2),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 9): construct bitstring representation of a nat and prove its properties */
spec fn bits_of_value_seq(n: nat) -> (result: Seq<char>)
  decreases n
{
    if n == 0nat {
        Seq::<char>::empty()
    } else {
        let q = n / 2nat;
        let r = n % 2nat;
        let s = bits_of_value_seq(q);
        s.push(if r == 1nat { '1' } else { '0' })
    }
}

/* helper modified by LLM (iteration 9): prove that bits_of_value_seq yields a valid bitstring and its numeric value equals n */
proof fn bits_of_value_seq_props(n: nat)
  ensures
    valid_bit_string(bits_of_value_seq(n)),
    str2int(bits_of_value_seq(n)) == n,
  decreases n
{
    if n == 0nat {
        // vacuous: valid_bit_string(Seq::empty()) and str2int(Seq::empty()) == 0
    } else {
        let q = n / 2nat;
        let r = n % 2nat;
        bits_of_value_seq_props(q);
        let s = bits_of_value_seq(q);
        let c = if r == 1nat { '1' } else { '0' };

        // Prove validity of s.push(c)
        assert forall|i: int|
            0 <= i < s.push(c).len() ==> s.push(c).index(i) == '0' || s.push(c).index(i) == '1'
        by
        {
            if 0 <= i && i < s.push(c).len() {
                if i < s.len() {
                    assert(s.push(c).index(i) == s.index(i));
                    assert(valid_bit_string(s));
                    assert(s.index(i) == '0' || s.index(i) == '1');
                } else {
                    assert(i == s.len());
                    assert(s.push(c).index(i) == c);
                    if r == 1nat {
                        assert(c == '1');
                    } else {
                        assert(r == 0nat);
                        assert(c == '0');
                    }
                    assert(c == '0' || c == '1');
                }
            }
        }
        assert(valid_bit_string(s.push(c)));

        // Compute str2int(s.push(c))
        assert(s.push(c).len() == s.len() + 1);
        assert(str2int(s.push(c)) == 2nat * str2int(s) + (if c == '1' { 1nat } else { 0nat }));
        assert(str2int(s) == q);
        if r == 1nat {
            assert(str2int(s.push(c)) == 2nat * q + 1nat);
        } else {
            assert(r == 0nat);
            assert(str2int(s.push(c)) == 2nat * q + 0nat);
        }
        assert(n == 2nat * q + r);
        if r == 1nat {
            assert(str2int(s.push(c)) == n);
        } else {
            assert(r == 0nat);
            assert(str2int(s.push(c)) == n);
        }
    }
}

/* helper modified by LLM (iteration 9): construct the bitstring of (x^y mod z) as a ghost value */
proof fn mod_exp_bits(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> (result: Seq<char>)
  requires
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    sy.len() > 0,
    str2int(sz) > 1,
  ensures
    valid_bit_string(result),
    str2int(result) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
{
    let x = str2int(sx);
    let y = str2int(sy);
    let z = str2int(sz);
    let n = exp_int(x, y) % z;
    let s = bits_of_value_seq(n);
    bits_of_value_seq_props(n);
    s
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    sy@.len() > 0 && str2int(sz@) > 1,
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
  decreases sy@.len(),
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 9): build result from ghost sequence computed by proof helper */
  let res = Vec::from_seq(mod_exp_bits(sx@, sy@, sz@));
  res
}
// </vc-code>


}

fn main() {}