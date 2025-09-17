use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed invariant block syntax */
exec fn vec_char_to_nat(v: &[char]) -> (res: nat)
    requires ValidBitString(v@)
    ensures res == Str2Int(v@)
{
    let mut n: nat = 0;
    for i in 0..v.len()
        invariant
            0 <= i <= v.len(),
            n == Str2Int(v@.subrange(0, i as int)),
    {
        let c = v[i];
        if c == '1' {
            n = n * 2 + 1;
        } else {
            n = n * 2;
        }
    }
    n
}

/* helper modified by LLM (iteration 2): fixed invariant block syntax */
exec fn nat_to_vec_char(n: nat, len: nat) -> (res: Vec<char>)
    ensures res@.len() == len as int
    ensures ValidBitString(res@)
    ensures Str2Int(res@) == n % (1 << len)
{
    let n_mod = n % (1 << len);
    let mut v = Vec::with_capacity(len as usize);
    let mut current = n_mod;
    for i in 0..len
        invariant
            0 <= i <= len,
            n_mod == Str2Int(v@) * (1 << (len - i)) + current,
            current < (1 << (len - i)),
    {
        let power = 1 << (len - 1 - i);
        if current >= power {
            v.push('1');
            current = current - power;
        } else {
            v.push('0');
        }
    }
    v
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): no changes needed */
    let max_len = if a.len() > b.len() { a.len() } else { b.len() };
    let a_int = vec_char_to_nat(a);
    let b_int = vec_char_to_nat(b);
    let modulus = 1 << max_len;
    let result_int = (a_int * b_int) % modulus;
    let res = nat_to_vec_char(result_int, max_len);
    res
}
// </vc-code>

fn main() {}
}

