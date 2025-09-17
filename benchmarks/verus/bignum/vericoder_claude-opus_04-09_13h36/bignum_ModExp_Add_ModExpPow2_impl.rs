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
        lemma_exp_one(x);
        lemma_exp_zero(x * x);
        assert(Exp_int(x, 2) == x * Exp_int(x, 1));
        assert(Exp_int(x, 1) == x);
        assert(Exp_int(x, 2) == x * x);
        assert(Exp_int(x * x, 1) == x * x);
        assert(y / 2 == 1);
        assert(Exp_int(x * x, y / 2) == x * x);
    } else {
        assert(y >= 4);
        assert((y - 2) % 2 == 0);
        assert((y - 2) > 0);
        lemma_exp_even(x, (y - 2) as nat);
        assert(Exp_int(x, (y - 2) as nat) == Exp_int(x * x, ((y - 2) / 2) as nat));
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        assert(Exp_int(x, (y - 1) as nat) == x * Exp_int(x, (y - 2) as nat));
        assert(Exp_int(x, y) == x * x * Exp_int(x, (y - 2) as nat));
        assert(Exp_int(x, y) == x * x * Exp_int(x * x, ((y - 2) / 2) as nat));
        assert((y - 2) / 2 == y / 2 - 1);
        assert(Exp_int(x * x, y / 2) == x * x * Exp_int(x * x, (y / 2 - 1) as nat));
        assert(Exp_int(x, y) == Exp_int(x * x, y / 2));
    }
}

proof fn lemma_exp_odd(x: nat, y: nat)
    requires y > 0, y % 2 == 1
    ensures Exp_int(x, y) == x * Exp_int(x * x, y / 2)
    decreases y
{
    if y == 1 {
        lemma_exp_one(x);
        lemma_exp_zero(x * x);
        assert(Exp_int(x, 1) == x);
        assert(Exp_int(x * x, 0) == 1);
        assert(x * Exp_int(x * x, 0) == x * 1 == x);
    } else {
        assert(y >= 3);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        assert((y - 1) % 2 == 0);
        lemma_exp_even(x, (y - 1) as nat);
        assert(Exp_int(x, (y - 1) as nat) == Exp_int(x * x, ((y - 1) / 2) as nat));
        assert((y - 1) / 2 == y / 2);
        assert(Exp_int(x, y) == x * Exp_int(x * x, y / 2));
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
        lemma_int2str_valid(n / 2);
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

proof fn lemma_str2int_bounds(s: Seq<char>, len: nat)
    requires ValidBitString(s), s.len() == len
    ensures Str2Int(s) < Exp_int(2, len)
    decreases len
{
    if len == 0 {
        assert(s.len() == 0);
        assert(Str2Int(s) == 0);
        assert(Exp_int(2, 0) == 1);
    } else {
        let s_prefix = s.subrange(0, s.len() - 1);
        lemma_str2int_bounds(s_prefix, (len - 1) as nat);
        assert(Str2Int(s_prefix) < Exp_int(2, (len - 1) as nat));
        assert(Str2Int(s) == 2 * Str2Int(s_prefix) + (if s.index(s.len() - 1) == '1' { 1nat } else { 0nat }));
        assert(Str2Int(s) <= 2 * Str2Int(s_prefix) + 1);
        assert(Str2Int(s) < 2 * Exp_int(2, (len - 1) as nat));
        assert(2 * Exp_int(2, (len - 1) as nat) == Exp_int(2, len));
    }
}

proof fn lemma_exp_64()
    ensures Exp_int(2, 64) == 18446744073709551616
{
    assert(Exp_int(2, 64) == 18446744073709551616) by(compute);
}

exec fn Int2Vec(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    let mut result = Vec::<char>::new();
    let mut m = n;
    
    proof {
        assert(result@ =~= seq![]);
        assert(Str2Int(seq![]) == 0);
    }
    
    while m > 0
        invariant 
            ValidBitString(result@),
            result@.len() <= 64,
            n == Str2Int(result@) + m * Exp_int(2, result@.len() as nat),
            m > 0 ==> result@.len() < 64
        decreases m
    {
        let old_m = m;
        let old_result_view = result@;
        
        if m % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        m = m / 2;
        
        proof {
            let new_result_view = result@;
            assert(new_result_view.subrange(0, new_result_view.len() - 1) =~= old_result_view);
            assert(new_result_view.index(new_result_view.len() - 1) == (if old_m % 2 == 1 { '1' } else { '0' }));
            assert(Str2Int(new_result_view) == 2 * Str2Int(old_result_view) + old_m % 2);
            assert(Exp_int(2, new_result_view.len() as nat) == 2 * Exp_int(2, old_result_view.len() as nat));
            assert(old_m == 2 * m + old_m % 2);
            assert(n == Str2Int(old_result_view) + old_m * Exp_int(2, old_result_view.len() as nat));
            assert(n == Str2Int(old_result_view) + (2 * m + old_m % 2) * Exp_int(2, old_result_view.len() as nat));
            assert(n == Str2Int(old_result_view) + old_m % 2 * Exp_int(2, old_result_view.len() as nat) + 
                       2 * m * Exp_int(2, old_result_view.len() as nat));
            assert(n == 2 * Str2Int(old_result_view) + old_m % 2 + m * Exp_int(2, new_result_view.len() as nat));
            assert(n == Str2Int(new_result_view) + m * Exp_int(2, new_result_view.len() as nat));
        }
    }
    
    proof {
        assert(m == 0);
        assert(n == Str2Int(result@));
    }
    
    result
}

exec fn Vec2Int(v: &[char]) -> (res: u64)
    requires ValidBitString(v@), v@.len() <= 64
    ensures res == Str2Int(v@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    proof {
        lemma_str2int_bounds(v@, v@.len() as nat);
        assert(Str2Int(v@) < Exp_int(2, v@.len() as nat));
        assert(v@.len() <= 64);
        assert(Str2Int(v@) < Exp_int(2, 64));
        lemma_exp_64();
    }
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            ValidBitString(v@),
            v@.len() <= 64,
            result == Str2Int(v@.subrange(0, i as int)),
            result <= u64::MAX / 2
        decreases v.len() - i
    {
        proof {
            let s_next = v@.subrange(0, i as int + 1);
            lemma_str2int_bounds(s_next, s_next.len() as nat);
            assert(s_next.len() <= 64);
            assert(Str2Int(s_next) < Exp_int(2, 64));
            lemma_exp_64();
        }
        
        let old_result = result;
        result = result * 2;
        if v[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
        
        proof {
            let s_prev = v@.subrange(0, i as int - 1);
            let s_curr = v@.subrange(0, i as int);
            assert(s_prev =~= s_curr.subrange(0, s_curr.len() - 1));
            assert(s_curr.index(s_curr.len() - 1) == v@[i as int - 1]);
            assert(Str2Int(s_curr) == 2 * Str2Int(s_prev) + (if v@[i as int - 1] == '1' { 1nat } else { 0nat }));
            assert(old_result == Str2Int(s_prev));
            assert(result == 2 * old_result + (if v@[i as int - 1] == '1' { 1u64 } else { 0u64 }));
            assert(result == Str2Int(s_curr));
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
        proof {
            assert(sy@.len() > 0);
            assert(false);
        }
        return Vec::<char>::new();
    }
    
    if sy.len() == 1 && sy[0] == '1' {
        proof {
            lemma_str2int_bounds(sx@, sx@.len() as nat);
            lemma_str2int_bounds(sz@, sz@.len() as nat);
        }
        let x_int = Vec2Int(sx);
        let z_int = Vec2Int(sz);
        let res_int = x_int % z_int;
        let res = Int2Vec(res_int);
        
        proof {
            assert(sy@ =~= seq!['1']);
            assert(Str2Int(sy@) == 1);
            lemma_exp_one(Str2Int(sx@));
            assert(Exp_int(Str2Int(sx@), 1) == Str2Int(sx@));
            assert(Str2Int(res@) == res_int);
            assert(res_int == x_int % z_int);
            assert(x_int == Str2Int(sx@));
            assert(z_int == Str2Int(sz@));
            assert(Str2Int(res@) == Str2Int(sx@) % Str2Int(sz@));
            assert(Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
        }
        return res;
    }
    
    let last_char = sy[sy.len() - 1];
    let sy_half = &sy[0..sy.len() / 2];
    
    let x_squared_int = Vec2Int(sx) * Vec2Int(sx) % Vec2Int(sz);
    let x_squared = Int2Vec(x_squared_int);
    
    let rec_result = ModExp_Add_ModExpPow2(&x_squared, sy_half, sz);
    
    let res = if last_char == '1' {
        let temp = Vec2Int(&rec_result) * Vec2Int(sx) % Vec2Int(sz);
        Int2Vec(temp)
    } else {
        rec_result
    };
    
    proof {
        let y_int = Str2Int(sy@);
        assert(y_int > 0);
        
        if y_int % 2 == 1 {
            lemma_exp_odd(Str2Int(sx@), y_int);
            assert(Exp_int(Str2Int(sx@), y_int) == Str2Int(sx@) * Exp_int(Str2Int(sx@) * Str2Int(sx@), y_int / 2));
        } else {
            lemma_exp_even(Str2Int(sx@), y_int);
            assert(Exp_int(Str2Int(sx@), y_int) == Exp_int(Str2Int(sx@) * Str2Int(sx@), y_int / 2));
        }
        
        assert(Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    
    res
}
// </vc-code>

fn main() {}
}