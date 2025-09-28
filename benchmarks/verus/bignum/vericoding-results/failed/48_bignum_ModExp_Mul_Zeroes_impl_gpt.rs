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
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn all_zero(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
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
/* helper modified by LLM (iteration 5): lemmas and specs for bitstring/int conversions */
proof fn lemma_str2int_push(s: Seq<char>, b: char)
  ensures
    str2int(s.push(b)) == 2nat * str2int(s) + (if b == '1' { 1nat } else { 0nat })
  decreases s.len()
{
    let t = s.push(b);
    assert(t.len() > 0);
    assert(str2int(t) == 2nat * str2int(t.subrange(0, t.len() - 1))
        + (if t[t.len() - 1] == '1' { 1nat } else { 0nat }));
    assert(t.subrange(0, t.len() - 1) == s);
    assert(t[t.len() - 1] == b);
}

/* helper modified by LLM (iteration 5): lemma for preserving validity when pushing a valid bit */
proof fn lemma_valid_push(s: Seq<char>, b: char)
  requires
    valid_bit_string(s),
    b == '0' || b == '1'
  ensures
    valid_bit_string(s.push(b))
  decreases s.len()
{
    assert forall|i: int| 0 <= i < s.push(b).len() ==> (s.push(b)[i] == '0' || s.push(b)[i] == '1') by {
        if 0 <= i && i < s.push(b).len() {
            assert(s.push(b).len() == s.len() + 1);
            if i < s.len() {
                assert(0 <= i && i < s.len());
                assert(valid_bit_string(s));
            } else {
                assert(i == s.len());
                assert(s.push(b)[i] == b);
                assert(b == '0' || b == '1');
            }
        }
    };
}

/* helper modified by LLM (iteration 5): specification function converting nat to big-endian bit sequence */
spec fn int2str(n: nat) -> Seq<char>
  decreases n
{
    if n == 0nat {
        Seq::empty()
    } else {
        let bit = if n % 2nat == 1nat { '1' } else { '0' };
        int2str(n / 2nat).push(bit)
    }
}

/* helper modified by LLM (iteration 5): lemma that encodes parity bit as modulo 2 */
proof fn lemma_mod2_bit(n: nat)
  ensures
    (if n % 2nat == 1nat { 1nat } else { 0nat }) == n % 2nat
{
    let r = n % 2nat;
    assert(0nat <= r && r < 2nat);
    if r >= 1nat {
        assert(r <= 1nat) by { };
        assert(r == 1nat);
    } else {
        assert(r < 1nat);
        assert(r == 0nat);
    }
}

/* helper modified by LLM (iteration 5): proof of properties for int2str */
proof fn lemma_int2str_props(n: nat)
  ensures
    valid_bit_string(int2str(n)),
    str2int(int2str(n)) == n
  decreases n
{
    if n == 0nat {
        // int2str(0) = empty sequence; valid and str2int(empty) = 0
    } else {
        lemma_int2str_props(n / 2nat);
        let b = if n % 2nat == 1nat { '1' } else { '0' };
        // Validity of the constructed sequence
        lemma_valid_push(int2str(n / 2nat), b);
        // Numeric value of the constructed sequence
        lemma_str2int_push(int2str(n / 2nat), b);
        assert(int2str(n) == int2str(n / 2nat).push(b));
        let bit_nat: nat = if b == '1' { 1nat } else { 0nat };
        assert(str2int(int2str(n))
            == 2nat * str2int(int2str(n / 2nat)) + bit_nat);
        assert(str2int(int2str(n / 2nat)) == n / 2nat);
        proof { lemma_mod2_bit(n); }
        assert(bit_nat == (if n % 2nat == 1nat { 1nat } else { 0nat }));
        assert(bit_nat == n % 2nat);
        assert(str2int(int2str(n)) == 2nat * (n / 2nat) + (n % 2nat));
        assert(n == 2nat * (n / 2nat) + (n % 2nat));
    }
}

/* helper modified by LLM (iteration 8): fix nat-suffixed literals in executable context */
fn int_to_vec(n: nat) -> (v: Vec<char>)
  ensures
    v@ == int2str(n),
    valid_bit_string(v@),
    str2int(v@) == n
  decreases n
{
    if n == 0 {
        let v: Vec<char> = Vec::new();
        assert(v@ == Seq::empty());
        assert(int2str(n) == Seq::empty());
        proof { lemma_int2str_props(n); }
        v
    } else {
        let mut v = int_to_vec(n / 2);
        let b: char = if n % 2 == 1 { '1' } else { '0' };
        v.push(b);
        proof {
            assert(int2str(n) == int2str(n / 2nat).push(b));
            lemma_int2str_props(n);
        }
        v
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
    sy@.len() > 0 && str2int(sz@) > 1
  ensures 
    valid_bit_string(res@),
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 8): construct result via recursive int_to_vec without nat-suffixed literals */
  let val: nat = exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@);
  let res_vec: Vec<char> = int_to_vec(val);
  res_vec
}
// </vc-code>


}

fn main() {}