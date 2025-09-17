use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
// Helper function to convert an integer to a binary string
proof fn int_to_binary_string_ensures(n: nat, res: Seq<char>)
    requires
        ValidBitString(res),
        Str2Int(res) == n,
    ensures
        ValidBitString(res),
        Str2Int(res) == n,
{
}

// Helper lemma for Str2Int properties
proof fn str2int_append_lemma(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        ValidBitString(s.push(c)),
        Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1 } else { 0 }),
    decreases s.len(),
{
    let new_s = s.push(c);
    assert(new_s.len() == s.len() + 1);
    assert(new_s.subrange(0, new_s.len() as int - 1) =~= s);
    assert(new_s.index(new_s.len() as int - 1) == c);
    assert(ValidBitString(new_s)) by {
        assert forall |i: int| 0 <= i && i < new_s.len() as int implies (new_s.index(i) == '0' || new_s.index(i) == '1') by {
            if i < s.len() as int {
                assert(new_s.index(i) == s.index(i));
            } else {
                assert(i == s.len() as int);
                assert(new_s.index(i) == c);
            }
        }
    }
}

// Lemma for empty string
proof fn str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0,
{
    assert(Seq::<char>::empty().len() == 0);
}
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    // Convert binary strings to integers
    let mut n1: nat = 0;
    let mut i: usize = 0;
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            ValidBitString(s1@),
            n1 == Str2Int(s1@.subrange(0, i as int)),
    {
        let digit = if s1[i] == '1' { 1nat } else { 0nat };
        n1 = n1 * 2 + digit;
        
        assert(s1@.subrange(0, (i + 1) as int) =~= s1@.subrange(0, i as int).push(s1@[i as int])) by {
            assert forall |j: int| 0 <= j < (i + 1) as int implies 
                s1@.subrange(0, (i + 1) as int)[j] == s1@.subrange(0, i as int).push(s1@[i as int])[j] by {
                if j < i as int {
                    assert(s1@.subrange(0, (i + 1) as int)[j] == s1@[j]);
                    assert(s1@.subrange(0, i as int)[j] == s1@[j]);
                    assert(s1@.subrange(0, i as int).push(s1@[i as int])[j] == s1@.subrange(0, i as int)[j]);
                } else {
                    assert(j == i as int);
                    assert(s1@.subrange(0, (i + 1) as int)[j] == s1@[j]);
                    assert(s1@.subrange(0, i as int).push(s1@[i as int])[j] == s1@[i as int]);
                }
            }
        };
        
        proof {
            str2int_append_lemma(s1@.subrange(0, i as int), s1@[i as int]);
        }
        
        i = i + 1;
    }
    assert(s1@.subrange(0, s1.len() as int) =~= s1@);
    
    let mut n2: nat = 0;
    let mut j: usize = 0;
    while j < s2.len()
        invariant
            0 <= j <= s2.len(),
            ValidBitString(s2@),
            n2 == Str2Int(s2@.subrange(0, j as int)),
    {
        let digit = if s2[j] == '1' { 1nat } else { 0nat };
        n2 = n2 * 2 + digit;
        
        assert(s2@.subrange(0, (j + 1) as int) =~= s2@.subrange(0, j as int).push(s2@[j as int])) by {
            assert forall |k: int| 0 <= k < (j + 1) as int implies 
                s2@.subrange(0, (j + 1) as int)[k] == s2@.subrange(0, j as int).push(s2@[j as int])[k] by {
                if k < j as int {
                    assert(s2@.subrange(0, (j + 1) as int)[k] == s2@[k]);
                    assert(s2@.subrange(0, j as int)[k] == s2@[k]);
                } else {
                    assert(k == j as int);
                    assert(s2@.subrange(0, (j + 1) as int)[k] == s2@[k]);
                }
            }
        };
        
        proof {
            str2int_append_lemma(s2@.subrange(0, j as int), s2@[j as int]);
        }
        
        j = j + 1;
    }
    assert(s2@.subrange(0, s2.len() as int) =~= s2@);
    
    // Multiply the integers
    let product = n1 * n2;
    
    // Convert result back to binary string
    let mut result = Vec::<char>::new();
    let mut temp = product;
    
    if temp == 0 {
        result.push('0');
        proof {
            str2int_empty();
            str2int_append_lemma(Seq::<char>::empty(), '0');
        }
    } else {
        while temp > 0
            invariant
                ValidBitString(result@.reverse()),
                temp * Exp_int(2, result.len() as nat) + Str2Int(result@.reverse()) == product,
                temp >= 0,
        {
            let digit_char = if temp % 2 == 1 { '1' } else { '0' };
            result.push(digit_char);
            
            proof {
                let old_rev = result@.subrange(0, result@.len() as int - 1).reverse();
                let new_rev = result@.reverse();
                
                assert(ValidBitString(old_rev));
                assert(new_rev =~= digit_char +:: old_rev) by {
                    assert forall |idx: int| 0 <= idx < new_rev.len() as int implies
                        new_rev[idx] == (digit_char +:: old_rev)[idx] by {
                        if idx == 0 {
                            assert(new_rev[0] == result@[result@.len() as int - 1]);
                            assert(result@[result@.len() as int - 1] == digit_char);
                        } else {
                            assert(new_rev[idx] == result@[result@.len() as int - 1 - idx]);
                            assert((digit_char +:: old_rev)[idx] == old_rev[idx - 1]);
                            assert(old_rev[idx - 1] == result@.subrange(0, result@.len() as int - 1)[result@.len() as int - 1 - idx]);
                        }
                    }
                };
                
                str2int_append_lemma(old_rev, digit_char);
                assert(Str2Int(new_rev) == 2 * Str2Int(old_rev) + (if digit_char == '1' { 1 } else { 0 }));
            }
            
            temp = temp / 2;
        }
        
        // Reverse the result to get correct order
        let mut k: usize = 0;
        let mut final_result = Vec::<char>::new();
        let n = result.len();
        
        while k < n
            invariant
                0 <= k <= n,
                n == result.len(),
                final_result.len() == k,
                ValidBitString(result@.reverse()),
                forall |idx: int| 0 <= idx < k as int ==> final_result@[idx] == result@[n as int - 1 - idx],
                ValidBitString(final_result@),
                k > 0 ==> Str2Int(final_result@) == Str2Int(result@.reverse().subrange(0, k as int)),
        {
            final_result.push(result[n - 1 - k]);
            
            proof {
                assert(final_result@[k as int] == result@[(n - 1 - k) as int]);
                if k > 0 {
                    let prev_subrange = result@.reverse().subrange(0, k as int);
                    let curr_subrange = result@.reverse().subrange(0, (k + 1) as int);
                    assert(curr_subrange =~= prev_subrange.push(result@.reverse()[k as int])) by {
                        assert forall |idx: int| 0 <= idx < (k + 1) as int implies
                            curr_subrange[idx] == prev_subrange.push(result@.reverse()[k as int])[idx] by {
                            if idx < k as int {
                                assert(curr_subrange[idx] == result@.reverse()[idx]);
                                assert(prev_subrange[idx] == result@.reverse()[idx]);
                            } else {
                                assert(idx == k as int);
                                assert(curr_subrange[idx] == result@.reverse()[k as int]);
                            }
                        }
                    };
                    str2int_append_lemma(prev_subrange, result@.reverse()[k as int]);
                } else {
                    assert(final_result@.len() == 1);
                    let curr_subrange = result@.reverse().subrange(0, 1);
                    assert(curr_subrange =~= Seq::<char>::empty().push(result@.reverse()[0])) by {
                        assert(curr_subrange.len() == 1);
                        assert(curr_subrange[0] == result@.reverse()[0]);
                    };
                    str2int_empty();
                    str2int_append_lemma(Seq::<char>::empty(), result@.reverse()[0]);
                    assert(Str2Int(final_result@) == Str2Int(curr_subrange));
                }
            }
            
            k = k + 1;
        }
        
        assert(final_result@ =~= result@.reverse()) by {
            assert forall |idx: int| 0 <= idx < final_result.len() as int implies
                final_result@[idx] == result@.reverse()[idx] by {
                assert(final_result@[idx] == result@[n as int - 1 - idx]);
                assert(result@.reverse()[idx] == result@[n as int - 1 - idx]);
            }
        };
        
        assert(Str2Int(final_result@) == product);
        return final_result;
    }
    
    assert(Str2Int(result@) == product);
    return result;
}
// </vc-code>

fn main() {}
}