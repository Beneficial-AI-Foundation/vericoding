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
spec fn Int2Str(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        Seq::empty()
    } else {
        Int2Str(n / 2) + seq![if n % 2 == 1 { '1' } else { '0' }]
    }
}

proof fn lemma_Str2Int_of_append(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        Str2Int(s + seq![c]) == 2 * Str2Int(s) + if c == '1' { 1 } else { 0 },
{
}

proof fn lemma_ValidBitString_Int2Str(n: nat)
    ensures
        ValidBitString(Int2Str(n)),
    decreases n
{
    if n > 0 {
        lemma_ValidBitString_Int2Str(n / 2);
    }
}

proof fn lemma_Str2Int_Int2Str(n: nat)
    ensures
        Str2Int(Int2Str(n)) == n,
    decreases n
{
    if n > 0 {
        lemma_ValidBitString_Int2Str(n / 2);
        lemma_Str2Int_Int2Str(n / 2);
        let rest = Int2Str(n / 2);
        let c = if n % 2 == 1 { '1' } else { '0' };
        lemma_Str2Int_of_append(rest, c);
    }
}

exec fn Str2Int_exec(s: &[char]) -> (r: nat)
    requires
        ValidBitString(s@),
    ensures
        r == Str2Int(s@),
    decreases s.len()
{
    if s.len() == 0 {
        return 0;
    }
    let last_idx = (s.len() - 1) as int;
    let prefix = s.subslice(0, last_idx);
    assert(ValidBitString(prefix@));
    let prefix_val = Str2Int_exec(prefix);
    let last = s[last_idx];
    let last_val = if last == '1' { 1nat } else { 0nat };
    2 * prefix_val + last_val
}

exec fn Int2Str_exec(n: nat) -> (res: Vec<char>)
    ensures
        res@ == Int2Str(n),
    decreases n
{
    if n == 0 {
        Vec::new()
    } else {
        let mut res = Int2Str_exec(n / 2);
        let c = if n % 2 == 1 { '1' } else { '0' };
        res.push(c);
        res
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_ModExpPow2_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    let a_val = Str2Int_exec(a);
    let b_val = Str2Int_exec(b);
    let sum_val = a_val + b_val;
    let res = Int2Str_exec(sum_val);
    lemma_ValidBitString_Int2Str(sum_val);
    res
}
// </vc-code>

fn main() {}
}

