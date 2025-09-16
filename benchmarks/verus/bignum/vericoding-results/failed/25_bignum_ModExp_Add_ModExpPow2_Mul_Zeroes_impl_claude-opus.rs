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
// Helper lemma to prove that concatenation of valid bit strings is valid
proof fn concat_valid_bit_strings(a: Seq<char>, b: Seq<char>)
    requires 
        ValidBitString(a),
        ValidBitString(b),
    ensures 
        ValidBitString(a + b)
{
    assert forall |i: int| 0 <= i && i < (a + b).len() as int implies
        ((a + b).index(i) == '0' || (a + b).index(i) == '1') by {
        if i < a.len() as int {
            assert((a + b).index(i) == a.index(i));
        } else {
            assert((a + b).index(i) == b.index(i - a.len() as int));
        }
    }
}

// Helper lemma to prove that appending a valid bit character maintains validity
proof fn append_valid_char(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        ValidBitString(s.push(c))
{
    assert forall |i: int| 0 <= i && i < s.push(c).len() as int implies
        (s.push(c).index(i) == '0' || s.push(c).index(i) == '1') by {
        if i < s.len() as int {
            assert(s.push(c).index(i) == s.index(i));
        } else {
            assert(i == s.len() as int);
            assert(s.push(c).index(i) == c);
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    let mut res = Vec::<char>::new();
    
    // Copy elements from a
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            res@.len() == i as int,
            ValidBitString(res@),
            forall |j: int| 0 <= j && j < i as int ==> res@.index(j) == a@.index(j),
            ValidBitString(a@),
        decreases a.len() - i
    {
        let c = a[i];
        proof {
            assert(0 <= i as int && i as int < a@.len());
            assert(ValidBitString(a@));
            assert(a@.index(i as int) == '0' || a@.index(i as int) == '1') by {
                assert(forall |k: int| 0 <= k && k < a@.len() ==> 
                    (a@.index(k) == '0' || a@.index(k) == '1'));
            }
            assert(c == a@.index(i as int));
            assert(c == '0' || c == '1');
            append_valid_char(res@, c);
        }
        res.push(c);
        i += 1;
    }
    
    // Copy elements from b
    let mut j = 0;
    while j < b.len()
        invariant
            0 <= j <= b.len(),
            res@.len() == a.len() + j,
            ValidBitString(res@),
            forall |k: int| 0 <= k && k < a.len() as int ==> res@.index(k) == a@.index(k),
            forall |k: int| a.len() as int <= k && k < res@.len() ==> 
                res@.index(k) == b@.index(k - a.len() as int),
            ValidBitString(b@),
        decreases b.len() - j
    {
        let c = b[j];
        proof {
            assert(0 <= j as int && j as int < b@.len());
            assert(ValidBitString(b@));
            assert(b@.index(j as int) == '0' || b@.index(j as int) == '1') by {
                assert(forall |k: int| 0 <= k && k < b@.len() ==> 
                    (b@.index(k) == '0' || b@.index(k) == '1'));
            }
            assert(c == b@.index(j as int));
            assert(c == '0' || c == '1');
            append_valid_char(res@, c);
        }
        res.push(c);
        j += 1;
    }
    
    // Prove the postcondition
    proof {
        concat_valid_bit_strings(a@, b@);
        assert(res@ == a@ + b@);
    }
    
    res
}
// </vc-code>

fn main() {}
}