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
proof fn lemma_exp_zero(x: nat)
    ensures Exp_int(x, 0) == 1
{
}

proof fn lemma_exp_one(x: nat)
    ensures Exp_int(x, 1) == x
{
    assert(Exp_int(x, 1) == x * Exp_int(x, 0) == x * 1 == x);
}

proof fn lemma_exp_even(x: nat, y: nat)
    requires y > 0, y % 2 == 0
    ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
    decreases y
{
    if y == 2 {
        assert(Exp_int(x, 2) == x * x * 1);
        assert(Exp_int(x * x, 1) == x * x);
    } else {
        assert(y >= 2);
        let half = y / 2;
        assert(half > 0);
        assert(half % 2 == 0 || half % 2 == 1);
        
        if half % 2 == 0 {
            lemma_exp_even(x * x, half);
        } else {
            lemma_exp_odd(x * x, half);
        }
    }
}

proof fn lemma_exp_odd(x: nat, y: nat)
    requires y > 0, y % 2 == 1
    ensures Exp_int(x, y) == x * Exp_int(x * x, y / 2)
    decreases y
{
    if y == 1 {
        lemma_exp_one(x);
        assert(Exp_int(x * x, 0) == 1);
    } else {
        let half = y / 2;
        assert(y == 2 * half + 1);
        assert(half > 0);
        
        if half % 2 == 0 {
            lemma_exp_even(x * x, half);
        } else {
            lemma_exp_odd(x * x, half);
        }
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

proof fn lemma_int2str_valid(n: nat)
    ensures ValidBitString(Int2Str(n))
    decreases n
{
    if n > 0 {
        lemma_int2str_valid(n / 2);
    }
}

proof fn lemma_str2int_int2str(n: nat)
    ensures Str2Int(Int2Str(n)) == n
    decreases n
{
    if n == 0 {
        assert(Int2Str(0) =~= seq![]);
        assert(Str2Int(seq![]) == 0);
    } else {
        lemma_str2int_int2str(n / 2);
        let s = Int2Str(n / 2);
        let full = s.push(if n % 2 == 1 { '1' } else { '0' });
        assert(full == Int2Str(n));
        assert(full.len() > 0);
        assert(full.subrange(0, full.len() - 1) =~= s);
        assert(full.index(full.len() - 1) == (if n % 2 == 1 { '1' } else { '0' }));
        assert(Str2Int(full) == 2 * Str2Int(s) + (if n % 2 == 1 { 1nat } else { 0nat }));
        assert(Str2Int(s) == n / 2);
        assert(Str2Int(full) == 2 * (n / 2) + n % 2);
        assert(2 * (n / 2) + n % 2 == n);
    }
}

exec fn Int2Vec(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    let mut result = Vec::<char>::new();
    let mut m = n;
    
    if m == 0 {
        proof {
            assert(result@ =~= seq![]);
            assert(Str2Int(seq![]) == 0);
        }
        return result;
    }
    
    while m > 0
        invariant 
            ValidBitString(result@),
            Str2Int(result@) + m * Exp_int(2, result@.len() as nat) == n,
            m > 0 ==> result@.len() < 64
        decreases m
    {
        let old_m = m;
        
        proof {
            let old_result_view = result@;
        }
        
        if m % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        m = m / 2;
        
        proof {
            let old_result_view = result@.subrange(0, result@.len() - 1);
            assert(result@.len() == old_result_view.len() + 1);
            assert(result@.subrange(0, result@.len() - 1) =~= old_result_view);
            assert(result@.index(result@.len() - 1) == (if old_m % 2 == 1 { '1' } else { '0' }));
            assert(Str2Int(result@) == 2 * Str2Int(old_result_view) + (if old_m % 2 == 1 { 1nat } else { 0nat }));
            assert(Str2Int(result@) == 2 * Str2Int(old_result_view) + old_m % 2);
            assert(m == old_m / 2);
            assert(Exp_int(2, result@.len() as nat) == 2 * Exp_int(2, old_result_view.len() as nat));
        }
    }
    
    proof {
        assert(m == 0);
        assert(Str2Int(result@) + 0 * Exp_int(2, result@.len() as nat) == n);
        assert(Str2Int(result@) == n);
    }
    
    result
}

exec fn Vec2Int(v: &[char]) -> (res: u64)
    requires ValidBitString(v@), v@.len() <= 64
    ensures res == Str2Int(v@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            ValidBitString(v@),
            result == Str2Int(v@.subrange(0, i as int))
    {
        let old_result = result;
        result = result * 2;
        if v[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
        
        proof {
            assert(v@.subrange(0, i as int).subrange(0, i as int - 1) =~= v@.subrange(0, i as int - 1));
            assert(v@.subrange(0, i as int).index(i as int - 1) == v@[i as int - 1]);
        }
    }
    
    proof {
        assert(v@.subrange(0, v@.len() as int) =~= v@);
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 0 {
        // y = 0, so x^y = 1
        let one = Int2Vec(1);
        let one_int = Vec2Int(&one);
        let z_int = Vec2Int(sz);
        let res_int = one_int % z_int;
        let res = Int2Vec(res_int);
        
        proof {
            lemma_int2str_valid(1nat);
            lemma_str2int_int2str(1nat);
            lemma_int2str_valid(res_int as nat);
            lemma_str2int_int2str(res_int as nat);
            assert(Str2Int(sy@) == 0);
            lemma_exp_zero(Str2Int(sx@));
            assert(Exp_int(Str2Int(sx@), 0) == 1);
        }
        
        return res;
    }
    
    // Check if y is even (last bit is 0) or odd (last bit is 1)
    let last_bit = sy[sy.len() - 1];
    
    if last_bit == '0' {
        // y is even: x^y = (x^2)^(y/2)
        let x_int = Vec2Int(sx);
        let x_squared = (x_int * x_int) % Vec2Int(sz);
        let x_squared_vec = Int2Vec(x_squared);
        
        // Create y/2 by removing the last bit
        let mut y_half = Vec::<char>::new();
        for i in 0..(sy.len() - 1)
            invariant 
                0 <= i <= sy.len() - 1,
                y_half@.len() == i,
                forall |j: int| 0 <= j && j < i ==> y_half@[j] == sy@[j],
                ValidBitString(y_half@)
        {
            y_half.push(sy[i]);
        }
        
        proof {
            assert(y_half@ =~= sy@.subrange(0, sy@.len() - 1));
            assert(Str2Int(sy@) % 2 == 0);
            assert(Str2Int(y_half@) == Str2Int(sy@) / 2);
            lemma_int2str_valid(x_squared as nat);
            lemma_str2int_int2str(x_squared as nat);
            lemma_exp_even(Str2Int(sx@), Str2Int(sy@));
        }
        
        let res = ModExp_Add_ModExpPow2(&x_squared_vec, &y_half, sz);
        
        proof {
            assert(Str2Int(res@) == Exp_int(x_squared as nat, Str2Int(y_half@)) % Str2Int(sz@));
            assert(Str2Int(x_squared_vec@) == x_squared);
            assert(Exp_int(x_squared as nat, Str2Int(y_half@)) % Str2Int(sz@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
        }
        
        return res;
    } else {
        // y is odd: x^y = x * (x^2)^((y-1)/2)
        let x_int = Vec2Int(sx);
        let z_int = Vec2Int(sz);
        let x_squared = (x_int * x_int) % z_int;
        let x_squared_vec = Int2Vec(x_squared);
        
        // Create (y-1)/2 by removing the last bit (which makes it y/2 when y is odd)
        let mut y_half = Vec::<char>::new();
        for i in 0..(sy.len() - 1)
            invariant 
                0 <= i <= sy.len() - 1,
                y_half@.len() == i,
                forall |j: int| 0 <= j && j < i ==> y_half@[j] == sy@[j],
                ValidBitString(y_half@)
        {
            y_half.push(sy[i]);
        }
        
        proof {
            assert(y_half@ =~= sy@.subrange(0, sy@.len() - 1));
            assert(Str2Int(sy@) % 2 == 1);
            assert(Str2Int(y_half@) == Str2Int(sy@) / 2);
            lemma_int2str_valid(x_squared as nat);
            lemma_str2int_int2str(x_squared as nat);
            lemma_exp_odd(Str2Int(sx@), Str2Int(sy@));
        }
        
        let temp = ModExp_Add_ModExpPow2(&x_squared_vec, &y_half, sz);
        let temp_int = Vec2Int(&temp);
        let res_int = (x_int * temp_int) % z_int;
        let res = Int2Vec(res_int);
        
        proof {
            assert(Str2Int(temp@) == Exp_int(x_squared as nat, Str2Int(y_half@)) % Str2Int(sz@));
            lemma_int2str_valid(res_int as nat);
            lemma_str2int_int2str(res_int as nat);
            assert(Str2Int(x_squared_vec@) == x_squared);
            assert(Exp_int(Str2Int(sx@), Str2Int(sy@)) == Str2Int(sx@) * Exp_int(x_squared as nat, Str2Int(y_half@)));
        }
        
        return res;
    }
}
// </vc-code>

fn main() {}
}