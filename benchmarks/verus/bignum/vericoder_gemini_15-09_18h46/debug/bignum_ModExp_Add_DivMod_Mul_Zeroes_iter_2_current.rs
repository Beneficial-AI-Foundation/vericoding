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
/* helper modified by LLM (iteration 2): Fixed type mismatches in both helpers by casting integer literals to nat. */
exec fn vec_to_nat(s: &[char]) -> (res: nat)
    requires
        ValidBitString(s@),
    ensures
        res == Str2Int(s@),
{
    let mut i: usize = 0;
    let mut res: nat = 0 as nat;
    while i < s.len()
        invariant
            ValidBitString(s@),
            0 <= i <= s.len(),
            res == Str2Int(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        let d = if s[i] == '1' { 1 as nat } else { 0 as nat };
        res = res * (2 as nat) + d;
        i = i + 1;
    }
    res
}

exec fn nat_to_vec(n: nat) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        (n == 0 && res@ == seq!['0']) || (n > 0 && Str2Int(res@) == n && res@[0] == '1'),
    decreases n
{
    if n == 0 as nat {
        vec!['0']
    } else if n == 1 as nat {
        vec!['1']
    } else {
        let mut prefix = nat_to_vec(n / (2 as nat));
        let last_char = if n % (2 as nat) == (1 as nat) { '1' } else { '0' };
        prefix.push(last_char);
        prefix
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Implement binary addition by converting to nat and back. */
    let a_val = vec_to_nat(a);
    let b_val = vec_to_nat(b);
    let sum = a_val + b_val;
    let res = nat_to_vec(sum);
    res
}
// </vc-code>

fn main() {}
}

