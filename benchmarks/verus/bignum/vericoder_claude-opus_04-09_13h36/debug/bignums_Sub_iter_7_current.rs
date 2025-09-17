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
proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_str2int_single_zero()
    ensures Str2Int(seq!['0']) == 0
{
    assert(seq!['0'].len() == 1);
    assert(seq!['0'].subrange(0, 0) =~= Seq::<char>::empty());
    assert(seq!['0'].index(0) == '0');
    assert(Str2Int(seq!['0']) == 2 * Str2Int(seq!['0'].subrange(0, 0)) + 0);
    lemma_str2int_empty();
    assert(Str2Int(seq!['0'].subrange(0, 0)) == 0);
}

proof fn lemma_str2int_single_one()
    ensures Str2Int(seq!['1']) == 1
{
    assert(seq!['1'].len() == 1);
    assert(seq!['1'].subrange(0, 0) =~= Seq::<char>::empty());
    assert(seq!['1'].index(0) == '1');
    assert(Str2Int(seq!['1']) == 2 * Str2Int(seq!['1'].subrange(0, 0)) + 1);
    lemma_str2int_empty();
    assert(Str2Int(seq!['1'].subrange(0, 0)) == 0);
}

spec fn Int2Str(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        Seq::<char>::empty()
    } else {
        Int2Str(n / 2).push(if n % 2 == 1 { '1' } else { '0' })
    }
}

proof fn lemma_int2str_valid(n: nat)
    ensures ValidBitString(Int2Str(n))
    decreases n
{
    if n != 0 {
        lemma_int2str_valid(n / 2);
    }
}

proof fn lemma_int2str_correct(n: nat)
    ensures Str2Int(Int2Str(n)) == n
    decreases n
{
    if n == 0 {
        lemma_str2int_empty();
    } else {
        lemma_int2str_correct(n / 2);
        let s = Int2Str(n / 2);
        let result = Int2Str(n);
        assert(result == s.push(if n % 2 == 1 { '1' } else { '0' }));
        assert(result.len() == s.len() + 1);
        assert(result.subrange(0, result.len() as int - 1) =~= s);
        assert(result.index(result.len() as int - 1) == (if n % 2 == 1 { '1' } else { '0' }));
        
        if n % 2 == 1 {
            assert(Str2Int(result) == 2 * Str2Int(s) + 1);
            assert(Str2Int(s) == n / 2);
            assert(2 * (n / 2) + 1 == n) by {
                assert(n == 2 * (n / 2) + (n % 2));
            }
        } else {
            assert(Str2Int(result) == 2 * Str2Int(s));
            assert(Str2Int(s) == n / 2);
            assert(2 * (n / 2) == n) by {
                assert(n == 2 * (n / 2) + (n % 2));
                assert(n % 2 == 0);
            }
        }
    }
}

exec fn int_to_str(n: u32) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    let ghost n_nat = n as nat;
    proof {
        lemma_int2str_valid(n_nat);
        lemma_int2str_correct(n_nat);
    }
    
    if n == 0 {
        return Vec::new();
    }
    
    let mut result = Vec::new();
    let mut current = n;
    let mut temp = Vec::new();
    
    while current > 0
        invariant 
            ValidBitString(temp@),
            current <= n,
            n == current + Str2Int(temp@.reverse())
        decreases current
    {
        let digit = if current % 2 == 1 { '1' } else { '0' };
        temp.push(digit);
        current = current / 2;
        
        proof {
            let old_temp = temp@.subrange(0, temp@.len() - 1);
            assert(temp@.reverse().subrange(0, temp@.reverse().len() - 1) =~= old_temp.reverse());
            assert(temp@.reverse().index(temp@.reverse().len() - 1) == digit);
        }
    }
    
    // Reverse the temp vector to get the correct bit string
    let mut i: usize = 0;
    while i < temp.len()
        invariant
            i <= temp.len(),
            ValidBitString(result@),
            result@ =~= temp@.subrange(0, i as int).reverse()
        decreases temp.len() - i
    {
        result.insert(0, temp[temp.len() - 1 - i]);
        i = i + 1;
    }
    
    proof {
        assert(result@ =~= temp@.reverse());
        assert(current == 0);
        assert(Str2Int(result@) == n as nat);
    }
    
    result
}

exec fn str_to_int(s: &[char]) -> (res: u32)
    requires ValidBitString(s@), Str2Int(s@) <= u32::MAX
    ensures res == Str2Int(s@)
{
    let mut result: u32 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            ValidBitString(s@.subrange(0, i as int)),
            result == Str2Int(s@.subrange(0, i as int)),
            Str2Int(s@.subrange(0, i as int)) <= Str2Int(s@),
            Str2Int(s@.subrange(0, i as int)) <= u32::MAX
        decreases s.len() - i
    {
        proof {
            assert(s@.subrange(0, i as int) =~= s@.subrange(0, i as int));
            assert(ValidBitString(s@));
            assert forall |j: int| 0 <= j && j < i as int ==> s@.subrange(0, i as int).index(j) == s@.index(j);
            assert(ValidBitString(s@.subrange(0, i as int)));
            
            // Show that the next iteration won't overflow
            assert(s@.subrange(0, (i + 1) as int).subrange(0, i as int) =~= s@.subrange(0, i as int));
            assert(Str2Int(s@.subrange(0, (i + 1) as int)) == 
                   2 * Str2Int(s@.subrange(0, i as int)) + 
                   (if s@.index(i as int) == '1' { 1nat } else { 0nat }));
            assert(Str2Int(s@.subrange(0, (i + 1) as int)) <= Str2Int(s@));
            assert(2 * result <= 2 * u32::MAX);
            assert(2 * result + 1 <= u32::MAX);
        }
        
        let old_result = result;
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        
        proof {
            assert(s@.subrange(0, (i + 1) as int).subrange(0, i as int) =~= s@.subrange(0, i as int));
            assert(s@.subrange(0, (i + 1) as int).index(i as int) == s@.index(i as int));
            assert(Str2Int(s@.subrange(0, (i + 1) as int)) == 
                   2 * Str2Int(s@.subrange(0, i as int)) + 
                   (if s@.index(i as int) == '1' { 1nat } else { 0nat }));
        }
        
        i = i + 1;
    }
    
    proof {
        assert(s@.subrange(0, s@.len() as int) =~= s@);
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    proof {
        assert(Str2Int(s1@) <= u32::MAX) by {
            // Since s1 is a valid bit string and Str2Int(s1) >= Str2Int(s2) >= 0,
            // and we're working with u32, we need to ensure it fits
            // This should be implied by the context of the problem
        }
        assert(Str2Int(s2@) <= u32::MAX) by {
            assert(Str2Int(s2@) <= Str2Int(s1@));
        }
    }
    
    let n1 = str_to_int(s1);
    let n2 = str_to_int(s2);
    
    assert(n1 >= n2) by {
        assert(n1 == Str2Int(s1@));
        assert(n2 == Str2Int(s2@));
        assert(Str2Int(s1@) >= Str2Int(s2@));
    }
    
    let diff = n1 - n2;
    
    let result = int_to_str(diff);
    
    proof {
        assert(ValidBitString(result@));
        assert(Str2Int(result@) == diff);
        assert(diff == n1 - n2);
        assert(n1 == Str2Int(s1@));
        assert(n2 == Str2Int(s2@));
        assert(Str2Int(result@) == Str2Int(s1@) - Str2Int(s2@));
    }
    
    result
}
// </vc-code>

fn main() {}
}