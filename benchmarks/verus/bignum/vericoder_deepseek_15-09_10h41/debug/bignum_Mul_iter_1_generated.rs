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
        
        assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if last_char == '1' { 1 } else { 0 }));
        assert(Str2Int(s.subrange(0, n as int)) * pow2((s.len() - n) as nat) == 2 * (Str2Int(s.subrange(0, n as int)) * pow2((s.len() - n - 1) as nat)));
    }
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        2 * pow2(n - 1)
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
{
    let mut result = Vec::<char>::new();
    let n1 = Str2Int(s1@);
    let n2 = Str2Int(s2@);
    
    let total_bits = (s1@.len() + s2@.len()) as usize;
    
    let mut i: usize = 0;
    while i < total_bits
        invariant
            ValidBitString(result@),
            Str2Int(result@) == n1 * (Str2Int(s2@) >> i),
            i <= total_bits,
        decreases total_bits - i
    {
        if i < s2@.len() as usize {
            if s2[i] == '1' {
                let mut temp = result.clone();
                let mut j: usize = 0;
                while j < s1@.len() as usize
                    invariant
                        ValidBitString(temp@),
                        Str2Int(temp@) == Str2Int(result@) + (n1 << j),
                        j <= s1@.len() as usize,
                    decreases s1@.len() as usize - j
                {
                    temp.push(s1[j]);
                    j += 1;
                }
                result = temp;
            }
        } else {
            result.push('0');
        }
        
        let mut carry = '0';
        let mut new_result = Vec::<char>::new();
        let mut k: usize = 0;
        while k < result.len()
            invariant
                ValidBitString(new_result@),
                Str2Int(new_result@) * 2 + (if carry == '1' { 1 } else { 0 }) == Str2Int(result@),
                k <= result.len(),
            decreases result.len() - k
        {
            if result[k] == '1' && carry == '1' {
                new_result.push('0');
                carry = '1';
            } else if result[k] == '1' || carry == '1' {
                new_result.push('1');
                carry = '0';
            } else {
                new_result.push('0');
                carry = '0';
            }
            k += 1;
        }
        
        if carry == '1' {
            new_result.push('1');
        }
        
        result = new_result;
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}


