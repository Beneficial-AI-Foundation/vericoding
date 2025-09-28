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

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): lemmas and builders for bitstring arithmetic and conversions */
proof fn lemma_str2int_push(s: Seq<char>, c: char)
    requires
        valid_bit_string(s),
        c == '0' || c == '1',
    ensures
        str2int(s.push(c)) == 2nat * str2int(s) + (if c == '1' { 1nat } else { 0nat }),
        valid_bit_string(s.push(c))
{
    assert(s.push(c).len() == s.len() + 1);

    assert(forall|i: int|
        0 <= i && i < s.push(c).len() ==> (s.push(c)[i] == '0' || s.push(c)[i] == '1')
    ) by {
        assert_forall_by(|i: int| {
            if 0 <= i && i < s.push(c).len() {
                if i < s.len() {
                    assert(s.push(c)[i] == s[i]);
                    assert(valid_bit_string(s));
                    assert(s[i] == '0' || s[i] == '1');
                } else {
                    assert(i == s.len());
                    assert(s.push(c)[i] == c);
                    assert(c == '0' || c == '1');
                }
            }
        });
    };
    assert(valid_bit_string(s.push(c)));

    assert(s.push(c).len() > 0);
    assert(s.push(c).subrange(0, s.push(c).len() - 1) == s);
    assert(s.push(c)[s.push(c).len() - 1] == c);
    assert(str2int(s.push(c))
        == 2nat * str2int(s) + (if c == '1' { 1nat } else { 0nat }));
}

/* helper modified by LLM (iteration 10): spec function converting a natural number to its bitstring (MSB-first) */
spec fn int2seq(n: nat) -> Seq<char>
    decreases n
{
    if n == 0nat {
        Seq::<char>::empty()
    } else {
        let q = n / 2nat;
        let r = n % 2nat;
        int2seq(q).push(if r == 1nat { '1' } else { '0' })
    }
}

/* helper modified by LLM (iteration 10): lemma proving properties of int2seq (valid bits and str2int round-trip) */
proof fn lemma_int2seq_props(n: nat)
    ensures
        valid_bit_string(int2seq(n)),
        str2int(int2seq(n)) == n,
    decreases n
{
    if n == 0nat {
        assert(valid_bit_string(int2seq(0nat)));
        assert(str2int(int2seq(0nat)) == 0nat);
    } else {
        let q = n / 2nat;
        let r = n % 2nat;
        lemma_int2seq_props(q);
        let c = if r == 1nat { '1' } else { '0' };
        lemma_str2int_push(int2seq(q), c);
        assert(int2seq(n) == int2seq(q).push(c));
        assert(valid_bit_string(int2seq(n)));
        assert(str2int(int2seq(n)) == 2nat * str2int(int2seq(q)) + (if c == '1' { 1nat } else { 0nat }));
        assert(str2int(int2seq(q)) == q);
        assert(n == 2nat * q + r);
        if r == 1nat {
            assert(2nat * q + (if c == '1' { 1nat } else { 0nat }) == 2nat * q + 1nat);
            assert(2nat * q + 1nat == n);
        } else {
            assert(r < 2nat && r != 1nat);
            assert(r == 0nat);
            assert(2nat * q + (if c == '1' { 1nat } else { 0nat }) == 2nat * q + 0nat);
            assert(2nat * q + 0nat == n);
        }
        assert(str2int(int2seq(n)) == n);
    }
}

/* helper modified by LLM (iteration 10): definitional spec for division with remainder over bitstring sequences */
spec fn div_mod_seq(dividend: Seq<char>, divisor: Seq<char>) -> (Seq<char>, Seq<char>)
    recommends
        valid_bit_string(dividend),
        valid_bit_string(divisor),
        str2int(divisor) > 0nat
{
    let n = str2int(dividend);
    let d = str2int(divisor);
    let q = n / d;
    let r = n % d;
    (int2seq(q), int2seq(r))
}
// </vc-helpers>

// <vc-spec>
fn div_mod(dividend: Vec<char>, divisor: Vec<char>) -> (result: (Vec<char>, Vec<char>))
  requires 
    valid_bit_string(dividend@) && valid_bit_string(divisor@),
    str2int(divisor@) > 0,
  ensures 
    valid_bit_string(result.0@) && valid_bit_string(result.1@),
    str2int(result.0@) == str2int(dividend@) / str2int(divisor@),
    str2int(result.1@) == str2int(dividend@) % str2int(divisor@),
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 10): build vectors using Vec::from_seq over int2seq results */
  let n = str2int(dividend@);
  let d = str2int(divisor@);
  let qn = n / d;
  let rn = n % d;
  proof {
      lemma_int2seq_props(qn);
      lemma_int2seq_props(rn);
  }
  let qv: Vec<char> = Vec::<char>::from_seq(int2seq(qn));
  let rv: Vec<char> = Vec::<char>::from_seq(int2seq(rn));
  (qv, rv)
}
// </vc-code>


}

fn main() {}