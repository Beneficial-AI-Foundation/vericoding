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
/* helper modified by LLM (iteration 4): Fix type errors by using nat instead of int in ghost code */
proof fn induction(n: nat)
    ensures
        true,
    decreases n
{
    if n > 0 {
        induction(n - 1);
    }
}

proof fn str2int_recursive_lemma(s: Seq<char>, n: nat)
    requires
        ValidBitString(s),
        n <= s.len(),
    ensures
        Str2Int(s) == Str2Int(s.subrange(0, n as int)) * pow2((s.len() - n) as nat) + Str2Int(s.subrange(n as int, s.len() as int)),
    decreases s.len() - n
{
    if n < s.len() {
        let s_prefix = s.subrange(0, n as int);
        let s_suffix = s.subrange(n as int, s.len() as int);
        
        assert(s_suffix.len() > 0);
        let last_char = s_suffix.index(s_suffix.len() as int - 1);
        
        str2int_recursive_lemma(s, n + 1);
        
        assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if last_char == '1' { 1nat } else { 0nat }));
        assert(Str2Int(s.subrange(0, n as int)) * pow2((s.len() - n) as nat) == 2 * (Str2Int(s.subrange(0, n as int)) * pow2((s.len() - n - 1) as nat)));
    }
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1nat
    } else {
        2nat * pow2(n - 1)
    }
}

proof fn pow2_properties()
    ensures
        forall |x: nat, y: nat| pow2(x + y) == pow2(x) * pow2(y),
        forall |n: nat| pow2(n) > 0
{
    assert forall |x: nat, y: nat| pow2(x + y) == pow2(x) * pow2(y) by {
        induction(x);
    };
    assert forall |n: nat| pow2(n) > 0 by {
        induction(n);
    };
}

proof fn str2int_zero_lemma()
    ensures
        forall |s: Seq<char>| ValidBitString(s) && s.len() == 0 ==> Str2Int(s) == 0
{
    assert forall |s: Seq<char>| ValidBitString(s) && s.len() == 0 implies Str2Int(s) == 0 by {
        let s = s;
        if ValidBitString(s) && s.len() == 0 {
            assert(Str2Int(s) == 0);
        }
    };
}
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fix type errors by using usize instead of int for array indices */
{
    let mut result = Vec::<char>::new();
    
    // Initialize result with zeros
    let total_len: usize = s1.len() + s2.len();
    let mut i: usize = 0;
    while i < total_len
        invariant
            i <= total_len,
            ValidBitString(result@),
            result@.len() == i
        decreases total_len - i
    {
        result.push('0');
        i += 1;
    }
    
    // Perform multiplication
    let mut i: usize = 0;
    while i < s1.len()
        invariant
            i <= s1.len(),
            ValidBitString(result@),
            result@.len() == total_len
        decreases s1.len() - i
    {
        let mut j: usize = 0;
        while j < s2.len()
            invariant
                j <= s2.len(),
                ValidBitString(result@),
                result@.len() == total_len
            decreases s2.len() - j
        {
            if s1[i] == '1' && s2[j] == '1' {
                let pos: usize = i + j;
                // Set the bit at position i+j
                let mut k: usize = pos;
                while k < total_len
                    invariant
                        k <= total_len,
                        ValidBitString(result@),
                        result@.len() == total_len
                    decreases total_len - k
                {
                    if result[k] == '0' {
                        result.set(k, '1');
                        break;
                    } else {
                        result.set(k, '0');
                        k += 1;
                    }
                }
            }
            j += 1;
        }
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}


