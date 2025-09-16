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
/* helper modified by LLM (iteration 2): fixed syntax of Str2Int_horner by removing requires clause, which is not valid on a spec function */
spec fn Str2Int_horner(s: Seq<char>, i: int) -> nat
    recommends
        ValidBitString(s),
        0 <= i <= s.len(),
    decreases i
{
    if i == 0 {
        0
    } else {
        Str2Int_horner(s, i - 1) * 2 + (if s[i - 1] == '1' { 1nat } else { 0nat })
    }
}

proof fn lemma_horner_subrange_dependency(s1: Seq<char>, s2: Seq<char>, i: int)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        0 <= i <= s1.len(),
        0 <= i <= s2.len(),
        s1.subrange(0, i) == s2.subrange(0, i),
    ensures Str2Int_horner(s1, i) == Str2Int_horner(s2, i)
    decreases i
{
    if i > 0 {
        lemma_horner_subrange_dependency(s1, s2, i-1);
    }
}

proof fn lemma_horner_equiv_Str2Int(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) == Str2Int_horner(s, s.len() as int)
    decreases s.len()
{
    if s.len() > 0 {
        let prefix = s.subrange(0, s.len() as int - 1);
        lemma_horner_equiv_Str2Int(prefix);
        lemma_horner_subrange_dependency(s, prefix, s.len() as int - 1);
    }
}

spec fn Int2Str(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq![]
    } else {
        Int2Str(n / 2).push(if n % 2 == 1 { '1' } else { '0' })
    }
}

proof fn lemma_ValidBitString_Int2Str(n: nat)
    ensures ValidBitString(Int2Str(n))
    decreases n
{
    if n > 0 {
        lemma_ValidBitString_Int2Str(n / 2);
    }
}

proof fn lemma_Str2Int_Int2Str(n: nat)
    ensures Str2Int(Int2Str(n)) == n
    decreases n
{
    if n > 0 {
        use vstd::arithmetic::div_mod::lemma_div_mod_reconstruct;
        lemma_Str2Int_Int2Str(n / 2);
        lemma_div_mod_reconstruct(n, 2);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): complete implementation via conversion to nat */
    let s1_seq = s1@;
    let s2_seq = s2@;

    let mut n1: nat = 0;
    let mut i: usize = 0;
    while i < s1.len()
        invariant
            ValidBitString(s1_seq),
            i <= s1.len(),
            n1 == Str2Int_horner(s1_seq, i as int),
    {
        n1 = n1 * 2 + (if s1[i] == '1' { 1 } else { 0 });
        i = i + 1;
    }
    lemma_horner_equiv_Str2Int(s1_seq);

    let mut n2: nat = 0;
    i = 0;
    while i < s2.len()
        invariant
            ValidBitString(s2_seq),
            i <= s2.len(),
            n2 == Str2Int_horner(s2_seq, i as int),
    {
        n2 = n2 * 2 + (if s2[i] == '1' { 1 } else { 0 });
        i = i + 1;
    }
    lemma_horner_equiv_Str2Int(s2_seq);

    let product = n1 * n2;

    let res_seq = Int2Str(product);
    lemma_ValidBitString_Int2Str(product);
    lemma_Str2Int_Int2Str(product);

    let mut res = Vec::with_capacity(res_seq.len() as usize);
    let mut k: usize = 0;
    while k < res_seq.len() as usize
        invariant
            res_seq == Int2Str(product),
            ValidBitString(res_seq),
            k <= res_seq.len() as usize,
            res@ == res_seq.subrange(0, k as int),
            ValidBitString(res@),
    {
        res.push(res_seq[k as int]);
        k = k + 1;
    }

    res
}
// </vc-code>

fn main() {}
}
