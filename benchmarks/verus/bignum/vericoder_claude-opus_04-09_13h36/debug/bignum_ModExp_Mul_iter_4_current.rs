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
spec fn Int2Str(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else if n == 1 {
        seq!['1']
    } else {
        Int2Str(n / 2).push(if n % 2 == 0 { '0' } else { '1' })
    }
}

proof fn lemma_int2str_valid(n: nat)
    ensures ValidBitString(Int2Str(n))
    decreases n
{
    if n <= 1 {
    } else {
        lemma_int2str_valid(n / 2);
    }
}

proof fn lemma_str2int_int2str(n: nat)
    ensures Str2Int(Int2Str(n)) == n
    decreases n
{
    if n == 0 {
    } else if n == 1 {
    } else {
        lemma_str2int_int2str(n / 2);
        let s = Int2Str(n / 2);
        assert(Int2Str(n) == s.push(if n % 2 == 0 { '0' } else { '1' }));
        assert(Str2Int(Int2Str(n)) == 2 * Str2Int(s) + if n % 2 == 0 { 0nat } else { 1nat });
        assert(Str2Int(s) == n / 2);
        assert(n == 2 * (n / 2) + n % 2);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let n1 = str2int_exec(s1);
    let n2 = str2int_exec(s2);
    let product = n1 * n2;
    
    proof {
        assert(n1 == Str2Int(s1@));
        assert(n2 == Str2Int(s2@));
        assert(product == Str2Int(s1@) * Str2Int(s2@));
    }
    
    let result = int2str_exec(product);
    
    proof {
        lemma_int2str_valid(product as nat);
        lemma_str2int_int2str(product as nat);
        assert(ValidBitString(result@));
        assert(Str2Int(result@) == product);
        assert(Str2Int(result@) == Str2Int(s1@) * Str2Int(s2@));
    }
    
    result
}

exec fn str2int_exec(s: &[char]) -> (res: u64)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(s@),
            result == Str2Int(s@.subrange(0, i as int))
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        
        assert(s@.subrange(0, (i + 1) as int) == s@.subrange(0, i as int).push(s@[i as int]));
        i = i + 1;
    }
    
    assert(s@.subrange(0, s.len() as int) == s@);
    result
}

exec fn int2str_exec(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        assert(v@ == seq!['0']);
        assert(Str2Int(v@) == 0);
        return v;
    }
    
    let mut result = Vec::new();
    let mut num = n;
    
    while num > 0
        invariant
            num <= n,
            ValidBitString(result@),
            n == num * Exp_int(2, result.len() as nat) + Str2Int(result@.reverse())
    {
        if num % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        num = num / 2;
    }
    
    reverse_vec(&mut result);
    
    proof {
        assert(num == 0);
        assert(n == Str2Int(result@));
    }
    
    result
}

exec fn reverse_vec(v: &mut Vec<char>)
    ensures v@ == old(v)@.reverse()
{
    let mut i: usize = 0;
    let mut j: usize = if v.len() > 0 { v.len() - 1 } else { 0 };
    
    while i < j
        invariant
            0 <= i <= v.len(),
            0 <= j < v.len(),
            i + j == v.len() - 1,
            forall|k: int| 0 <= k < i as int ==> v@[k] == old(v)@[(v.len() - 1 - k) as int],
            forall|k: int| (j as int) < k < v.len() as int ==> v@[k] == old(v)@[(v.len() - 1 - k) as int],
            forall|k: int| i as int <= k <= j as int ==> v@[k] == old(v)@[k]
    {
        let temp = v[i];
        v.set(i, v[j]);
        v.set(j, temp);
        i = i + 1;
        j = j - 1;
    }
}
// </vc-code>

fn main() {}
}