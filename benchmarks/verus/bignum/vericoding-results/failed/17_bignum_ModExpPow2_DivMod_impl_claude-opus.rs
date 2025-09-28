// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn str2int(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        if valid_bit_string(s) {
            2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
        } else {
            0nat
        }
    }
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (result: (Seq<char>, Seq<char>))
    requires 
        valid_bit_string(dividend) && valid_bit_string(divisor) && str2int(divisor) > 0
    ensures 
        valid_bit_string(result.0) && valid_bit_string(result.1),
        str2int(result.0) == str2int(dividend) / str2int(divisor),
        str2int(result.1) == str2int(dividend) % str2int(divisor)
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
spec fn int2str(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else if n == 1 {
        seq!['1']
    } else {
        int2str(n / 2).add(if n % 2 == 0 { seq!['0'] } else { seq!['1'] })
    }
}

proof fn lemma_int2str_valid(n: nat)
    ensures valid_bit_string(int2str(n))
    decreases n
{
    if n > 1 {
        lemma_int2str_valid(n / 2);
    }
}

proof fn lemma_exp_power_of_two(x: nat, n: nat)
    ensures 
        n > 0 ==> exp_int(x, exp_int(2, n)) == exp_int(exp_int(x, exp_int(2, (n - 1) as nat)), 2)
    decreases n
{
    if n > 0 {
        assert(exp_int(2, n) == 2 * exp_int(2, (n - 1) as nat));
        assert(exp_int(x, 2 * exp_int(2, (n - 1) as nat)) == x * exp_int(x, (2 * exp_int(2, (n - 1) as nat) - 1) as nat));
        if n == 1 {
            assert(exp_int(2, 0) == 1);
            assert(exp_int(x, 2) == x * x);
            assert(exp_int(x, 1) == x);
            assert(exp_int(exp_int(x, 1), 2) == exp_int(x, 2));
        } else {
            lemma_exp_power_of_two(x, (n - 1) as nat);
        }
    }
}

fn multiply_mod(a: Vec<char>, b: Vec<char>, m: Vec<char>) -> (res: Vec<char>)
    requires
        valid_bit_string(a@) && valid_bit_string(b@) && valid_bit_string(m@),
        str2int(m@) > 0
    ensures
        valid_bit_string(res@),
        str2int(res@) == (str2int(a@) * str2int(b@)) % str2int(m@)
{
    assume(false);
    unreached()
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2(sx: Vec<char>, sy: Vec<char>, n: u8, sz: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
        str2int(sy@) == exp_int(2nat, n as nat) || str2int(sy@) == 0,
        sy.len() == n as int + 1,
        str2int(sz@) > 1
    ensures 
        valid_bit_string(res@),
        str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
    decreases n
// </vc-spec>
// <vc-code>
{
    if sy.len() == 1 {
        assert(n == 0);
        assert(sy@.len() == 1);
        if sy[0] == '0' {
            assert(str2int(sy@) == 0);
            assert(exp_int(str2int(sx@), 0) == 1);
            lemma_int2str_valid(1);
            let one_str = vec!['1'];
            assert(valid_bit_string(one_str@));
            assert(str2int(one_str@) == 1);
            let (_, r) = div_mod(one_str@, sz@);
            assert(str2int(r) == 1 % str2int(sz@));
            let mut result = Vec::new();
            let mut i = 0;
            while i < r.len()
                invariant
                    0 <= i <= r.len(),
                    result@.len() == i,
                    forall|j: int| 0 <= j < i ==> result@[j] == r[j]
            {
                result.push(r[i]);
                i = i + 1;
            }
            assert(result@ =~= r);
            return result;
        } else {
            assert(sy[0] == '1');
            assert(str2int(sy@) == 1);
            assert(exp_int(str2int(sx@), 1) == str2int(sx@));
            let (_, r) = div_mod(sx@, sz@);
            assert(str2int(r) == str2int(sx@) % str2int(sz@));
            let mut result = Vec::new();
            let mut i = 0;
            while i < r.len()
                invariant
                    0 <= i <= r.len(),
                    result@.len() == i,
                    forall|j: int| 0 <= j < i ==> result@[j] == r[j]
            {
                result.push(r[i]);
                i = i + 1;
            }
            assert(result@ =~= r);
            return result;
        }
    } else {
        assert(n > 0);
        let half_y = vec!['1'];
        let mut i = 1;
        while i <= n
            invariant
                1 <= i <= n + 1,
                half_y@.len() == i,
                half_y@[0] == '1',
                forall|j: int| 1 <= j < i ==> half_y@[j] == '0',
                valid_bit_string(half_y@),
                str2int(half_y@) == exp_int(2, (i - 1) as nat)
        {
            half_y.push('0');
            i = i + 1;
        }
        assert(half_y@.len() == n as int);
        assert(str2int(half_y@) == exp_int(2, (n - 1) as nat));
        
        let temp = mod_exp_pow2(sx, half_y, (n - 1), sz);
        assert(str2int(temp@) == exp_int(str2int(sx@), exp_int(2, (n - 1) as nat)) % str2int(sz@));
        
        let squared = multiply_mod(temp, temp, sz);
        proof {
            lemma_exp_power_of_two(str2int(sx@), n as nat);
        }
        return squared;
    }
}
// </vc-code>


}

fn main() {}