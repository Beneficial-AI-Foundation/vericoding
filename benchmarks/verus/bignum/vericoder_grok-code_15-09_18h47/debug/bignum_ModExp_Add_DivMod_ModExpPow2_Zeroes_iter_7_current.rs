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
/* helper modified by LLM (iteration 7): named return to fix result scope */
spec fn power2(exp: int) -> int
    requires exp >= 0
    decreases exp
{
    if exp == 0 { 1 } else { 2 * power2(exp - 1) }
}

/* helper modified by LLM (iteration 7): named return to fix result scope */
exec fn str_to_nat(s: &[char]) -> (result: int)
    requires ValidBitString(s@)
    ensures
        result >= 0,
        result as nat == Str2Int(s@)
{
    let mut res: int = 0;
    let mut pow: int = 1;
    let mut i = s.len();
    while i > 0
        invariant
            0 <= i <= s.len(),
            pow >= 1,
            res >= 0,
            (power2((s.len() as int) - (i as int)) as nat) == pow as nat,
            (res as nat) == Str2Int(s@.subrange(i as int, s.len() as int)),
        decreases i
    {
        i = i - 1;
        if s[i] == '1' {
            res = res + pow;
        }
        pow = 2 * pow;
    }
    return res;
}

/* helper modified by LLM (iteration 7): named return to fix result scope */
exec fn nat_to_binary(n: int) -> (result: Vec<char>)
    requires n >= 0
    ensures
        ValidBitString(result@),
        Str2Int(result@) == n as nat
{
    if n == 0 {
        let mut res = Vec::<char>::new();
        res.push('0');
        return res;
    } else {
        let mut res = nat_to_binary(n / 2);
        if n % 2 == 0 {
            res.push('0');
        } else {
            res.push('1');
        }
        return res;
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_ModExpPow2_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 7): implemented addition using fixed helpers */
{
    let a_nat = str_to_nat(a);
    let b_nat = str_to_nat(b);
    let sum = a_nat + b_nat;
    return nat_to_binary(sum);
}
// </vc-code>

fn main() {}
}

