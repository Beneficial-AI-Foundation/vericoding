// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed type casting in modulo operations */
spec fn int2str_helper(n: nat, len: nat) -> Seq<char>
    decreases len
{
    if len == 0 {
        Seq::empty()
    } else {
        let rest = int2str_helper(n / 2, (len - 1) as nat);
        let bit = if n % 2 == 0 { '0' } else { '1' };
        rest.push(bit)
    }
}

proof fn int2str_helper_ensures(n: nat, len: nat)
    ensures
        int2str_helper(n, len).len() == len,
        valid_bit_string(int2str_helper(n, len)),
        str2int(int2str_helper(n, len)) == n % pow2(len),
    decreases len
{
    if len == 0 {
        assert(int2str_helper(n, len) == Seq::<char>::empty());
        assert(str2int(Seq::<char>::empty()) == 0);
        assert(n % pow2(0) == n % 1 == 0);
    } else {
        let rest = int2str_helper(n / 2, (len - 1) as nat);
        let bit = if n % 2 == 0 { '0' } else { '1' };
        int2str_helper_ensures(n / 2, (len - 1) as nat);
        assert(rest.len() == len - 1);
        assert(valid_bit_string(rest));
        assert(str2int(rest) == (n / 2) % pow2((len - 1) as nat));
        
        let full = rest.push(bit);
        assert(full.len() == len);
        assert(full.subrange(0, len - 1) == rest);
        assert(full[len - 1] == bit);
        
        assert(str2int(full) == 2 * str2int(rest) + (if bit == '1' { 1nat } else { 0nat })) by {
            reveal(str2int);
        }
        
        assert((n / 2) % pow2((len - 1) as nat) == (n / 2) % pow2((len - 1) as nat));
        assert(2 * ((n / 2) % pow2((len - 1) as nat)) + (n % 2) == n % pow2(len)) by {
            assert(pow2(len) == 2 * pow2((len - 1) as nat));
        }
    }
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

fn compute_bit_length(n: u64) -> (len: u64)
    ensures
        n < pow2(len as nat),
        len > 0 ==> n >= pow2((len - 1) as nat) || n == 0,
{
    if n == 0 {
        return 1;
    }
    
    let mut len: u64 = 0;
    let mut power: u64 = 1;
    
    while power <= n && power < u64::MAX / 2
        invariant
            power == pow2(len as nat),
            power > 0,
            len < 64,
            n >= power / 2 || len == 0,
        decreases u64::MAX - power
    {
        len = len + 1;
        power = power * 2;
    }
    
    if power > n {
        len
    } else {
        64
    }
}

fn int2str(n: u64) -> (res: Vec<char>)
    ensures
        valid_bit_string(res@),
        str2int(res@) == n,
{
    if n == 0 {
        let mut res = Vec::new();
        res.push('0');
        proof {
            assert(res@.len() == 1);
            assert(res@[0] == '0');
            assert(valid_bit_string(res@));
            assert(str2int(res@) == 0) by {
                reveal(str2int);
                assert(res@.subrange(0, 0) == Seq::<char>::empty());
            }
        }
        res
    } else {
        let len = compute_bit_length(n);
        let mut res = Vec::new();
        let mut remaining = n;
        let mut i: u64 = 0;
        
        while i < len && remaining > 0
            invariant
                i <= len,
                res.len() == i,
                valid_bit_string(res@),
                i > 0 ==> str2int(res@) == (n as nat) % pow2(i as nat),
                i == 0 ==> str2int(res@) == 0,
                remaining == ((n as nat) / pow2(i as nat)) as u64,
            decreases len - i
        {
            let bit = if remaining % 2 == 0 { '0' } else { '1' };
            res.push(bit);
            
            proof {
                assert(res@.subrange(0, i as int) == res@.subrange(0, i as int));
                if i > 0 {
                    assert(str2int(res@.subrange(0, i as int)) == (n as nat) % pow2(i as nat));
                }
                assert(res@[i as int] == bit);
                assert(str2int(res@) == 2 * str2int(res@.subrange(0, i as int)) + (if bit == '1' { 1nat } else { 0nat })) by {
                    reveal(str2int);
                }
            }
            
            remaining = remaining / 2;
            i = i + 1;
        }
        
        while i < len
            invariant
                i <= len,
                res.len() == i,
                valid_bit_string(res@),
                str2int(res@) == n,
            decreases len - i
        {
            res.push('0');
            proof {
                assert(str2int(res@) == n) by {
                    reveal(str2int);
                }
            }
            i = i + 1;
        }
        
        res
    }
}
// </vc-helpers>

// <vc-spec>
fn sub(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@),
    str2int(s1@) >= str2int(s2@),
  ensures 
    valid_bit_string(res@),
    str2int(res@) == str2int(s1@) - str2int(s2@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fixed type issues in binary subtraction */
    let mut n1: u64 = 0;
    let mut n2: u64 = 0;
    let mut power: u64 = 1;
    let mut i: usize = 0;
    
    // Convert s1 to integer
    while i < s1.len() && power <= u64::MAX / 2
        invariant
            i <= s1.len(),
            power == pow2(i as nat),
            n1 == str2int(s1@.subrange(0, i as int)),
            power > 0,
        decreases s1.len() - i
    {
        if s1[i] == '1' {
            if n1 <= u64::MAX - power {
                n1 = n1 + power;
            }
        }
        if power <= u64::MAX / 2 {
            power = power * 2;
        }
        i = i + 1;
    }
    
    proof {
        assert(s1@.subrange(0, s1.len() as int) == s1@);
        assert(n1 == str2int(s1@));
    }
    
    // Convert s2 to integer
    i = 0;
    power = 1;
    while i < s2.len() && power <= u64::MAX / 2
        invariant
            i <= s2.len(),
            power == pow2(i as nat),
            n2 == str2int(s2@.subrange(0, i as int)),
            power > 0,
        decreases s2.len() - i
    {
        if s2[i] == '1' {
            if n2 <= u64::MAX - power {
                n2 = n2 + power;
            }
        }
        if power <= u64::MAX / 2 {
            power = power * 2;
        }
        i = i + 1;
    }
    
    proof {
        assert(s2@.subrange(0, s2.len() as int) == s2@);
        assert(n2 == str2int(s2@));
    }
    
    let diff = n1 - n2;
    let res = int2str(diff);
    
    proof {
        assert(str2int(res@) == diff);
        assert(diff == str2int(s1@) - str2int(s2@));
    }
    
    res
}
// </vc-code>


}

fn main() {}