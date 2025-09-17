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
/* helper modified by LLM (iteration 3): no change */
proof fn lemma_Str2Int_of_zero_prefixed(s: Seq<char>)
    requires
        ValidBitString(s),
    ensures
        Str2Int(seq!['0'] + s) == Str2Int(s),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_Str2Int_of_zero_prefixed(s.subrange(0, (s.len() - 1) as int));
    }
}

proof fn lemma_remove_leading_zeros(s: Seq<char>, k: nat)
    requires
        k <= s.len(),
        ValidBitString(s),
        forall|i: int| 0 <= i < k ==> s[i] == '0',
    ensures
        Str2Int(s) == Str2Int(s.subrange(k as int, s.len() as int)),
    decreases k
{
    if k > 0 {
        let s_tail = s.subrange(1, s.len() as int);
        lemma_Str2Int_of_zero_prefixed(s_tail);
        lemma_remove_leading_zeros(s_tail, (k - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Bignums_Sub_NormalizeBitstring(s: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added missing decreases clauses to loops */
    let mut i: usize = 0;
    while i < s.len() && s[i] == '0'
        invariant
            0 <= i <= s.len(),
            ValidBitString(s@),
            forall|j: int| 0 <= j < i ==> s@[j] == '0',
        decreases s.len() - i
    {
        i = i + 1;
    }

    if i == s.len() {
        proof {
            lemma_remove_leading_zeros(s@, s.len() as nat);
        }
        let mut res = Vec::new();
        res.push('0');
        assert(Str2Int(res@) == Str2Int(s@));
        return res;
    } else {
        proof {
            lemma_remove_leading_zeros(s@, i as nat);
        }

        let mut res = Vec::new();
        let mut k = i;
        while k < s.len()
            invariant
                i < s.len(),
                i <= k <= s.len(),
                ValidBitString(s@),
                res@ == s@.subrange(i as int, k as int),
                ValidBitString(res@),
            decreases s.len() - k
        {
            res.push(s[k]);
            k = k + 1;
        }

        assert(res@ == s@.subrange(i as int, s.len() as int));
        assert(Str2Int(res@) == Str2Int(s@));
        return res;
    }
}
// </vc-code>

fn main() {}
}
