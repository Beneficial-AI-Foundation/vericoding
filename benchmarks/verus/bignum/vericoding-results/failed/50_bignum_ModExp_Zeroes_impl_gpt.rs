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

spec fn all_zero(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
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
/* helper modified by LLM (iteration 10): define nat2bits and lemmas to relate it to str2int and bit-string validity */
spec fn nat2bits(n: nat) -> Seq<char>
  decreases n
{
  if n == 0 {
    Seq::empty()
  } else {
    let b: char = if n % 2 == 1nat { '1' } else { '0' };
    nat2bits(n / 2).push(b)
  }
}

proof fn lemma_str2int_push(s: Seq<char>, c: char)
  ensures
    str2int(s.push(c)) == 2nat * str2int(s) + (if c == '1' { 1nat } else { 0nat })
{
  let sp = s.push(c);
  assert(sp.len() > 0);
  assert(str2int(sp) == 2nat * str2int(sp.subrange(0, sp.len() - 1))
    + (if sp[sp.len() - 1] == '1' { 1nat } else { 0nat }));
  assert(sp.subrange(0, sp.len() - 1) == s);
  assert(sp[sp.len() - 1] == c);
}

proof fn lemma_nat2bits_props(n: nat)
  ensures
    str2int(nat2bits(n)) == n,
    valid_bit_string(nat2bits(n))
  decreases n
{
  if n == 0 {
  } else {
    let q = n / 2;
    let r = n % 2;
    lemma_nat2bits_props(q);
    let b: char = if r == 1nat { '1' } else { '0' };

    lemma_str2int_push(nat2bits(q), b);
    assert(str2int(nat2bits(n))
      == 2nat * str2int(nat2bits(q)) + (if b == '1' { 1nat } else { 0nat }));
    if r == 1nat { assert(b == '1'); } else { assert(b == '0'); }
    assert(str2int(nat2bits(n)) == 2nat * str2int(nat2bits(q)) + r);
    assert(str2int(nat2bits(q)) == q);
    assert(2nat * q + r == n);

    let sp = nat2bits(n);
    let pre = nat2bits(q);
    assert(sp == pre.push(b));
    assert_forall_by(|i: int| {
      requires(0 <= i < sp.len());
      ensures(sp[i] == '0' || sp[i] == '1');
      if i < pre.len() {
        assert(sp == pre.push(b));
        assert(pre.push(b)[i] == pre[i]);
        assert(sp[i] == pre[i]);
        assert(valid_bit_string(pre));
        assert(0 <= i && i < pre.len());
        assert(pre[i] == '0' || pre[i] == '1');
      } else {
        assert(i == pre.len());
        assert(sp == pre.push(b));
        assert(pre.push(b)[i] == b);
        assert(sp[i] == b);
        if r == 1nat { assert(b == '1'); } else { assert(b == '0'); }
      }
    });
  }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
    sy@.len() > 0 && str2int(sz@) > 1,
  ensures
    valid_bit_string(res@),
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): build Vec<char> from Seq<char> (nat2bits) using a loop */
    let ghost x = str2int(sx@);
    let ghost y = str2int(sy@);
    let ghost z = str2int(sz@);
    let ghost r = exp_int(x, y) % z;

    lemma_nat2bits_props(r);

    let s = nat2bits(r);
    let n: int = s.len();
    let mut v: Vec<char> = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant
            0 <= i <= n,
            v@ == s.subrange(0, i),
        decreases n - i
    {
        let c = s[i];
        let ghost prev = v@;
        let ghost j = i;
        v.push(c);
        proof {
            assert(v@ == prev.push(c));
            assert(prev == s.subrange(0, j));
            assert(s.subrange(0, j).push(c) == s.subrange(0, j + 1));
        }
        i = i + 1;
    }
    let res = v;
    proof {
        assert(i == n);
        assert(res@ == s);
        assert(valid_bit_string(s));
        assert(valid_bit_string(res@));
        assert(str2int(s) == r);
        assert(str2int(res@) == r);
    }
    res
}
// </vc-code>


}

fn main() {}