use vstd::prelude::*;

verus! {

spec fn f2(n: nat) -> nat 
    decreases n
{
    if n == 0 { 0 }
    else { 5 * f2(n / 3) + n % 4 }
}

// <vc-helpers>
proof fn f2_mono(x: nat, y: nat)
    requires
        x <= y,
    ensures
        f2(x) <= f2(y),
    decreases y
{
    if x < y {
        if y > 0 {
            let sub = (y / 3) as nat;
            if sub > 0 {
                f2_mono(x / 3, y / 3);
            }
        }
    }
}

spec fn seq_sum(s: Seq<u32>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[s.len() - 1] as nat + seq_sum(s.drop_last(1))
    }
}

spec fn seq_drop_last(s: Seq<u32>, n: int) -> Seq<u32>
    requires 0 <= n && n <= s.len()
    ensures result@ == s@.drop_last(n)
{
    if n == 0 {
        s
    } else {
        seq_drop_last(s.drop_last(1), n - 1)
    }
}

spec fn pow3(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 3 * pow3(n - 1) }
}

spec fn pow5(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 5 * pow5(n - 1) }
}

proof fn seq_drop_last_proof(s: Seq<u32>, n: int)
    requires
        0 <= n && n <= s.len(),
    ensures
        seq_drop_last(s, n)@ == s@.drop_last(n)
{
    if n > 0 {
        seq_drop_last_proof(s.drop_last(1), n - 1);
    }
}

proof fn pow5_proof(m: nat, n: nat)
    requires
        m == n,
    ensures
        pow5(m) == pow5(n)
{
}
// </vc-helpers>

// <vc-spec>
fn mod2(n: u32) -> (a: u32)
    ensures a == f2(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut a: u32 = 0;
    let mut n_mut = n;
    let mut i: nat = 0;
    let mut stack: Seq<u32> = Seq::empty();
    
    while i < 100
        invariant
            i <= 100,
            n_mut as nat <= n as nat,
            stack.len() == i,
            forall |k: int| 0 <= k && k < i ==> (#[trigger] stack[k]) as nat == (n as nat) / pow3(k) % 4,
            a as nat == 5 * (if i > 0 { seq_sum(stack.drop_last(1)) } else { 0 }) + ((n as nat) % 4) * i
    {
        if n_mut == 0 {
            break;
        }
        let remainder = n_mut % 4;
        stack = stack.push(remainder);
        a = a + remainder;
        n_mut = n_mut / 3;
        i = i + 1;
    }
    
    let mut total: u32 = 0;
    let mut pow: nat = pow5(i);
    let mut j: nat = i;
    
    while j > 0
        invariant
            0 <= j && j <= i,
            total as nat == pow5(i - j) * seq_sum(seq_drop_last(stack, j)),
            pow == pow5(i - j)
    {
        j = j - 1;
        proof {
            let prev_total: nat = total as nat;
            let prev_pow: nat = pow;
            pow = pow / 5;
            total = (5 * total + stack@[j]) as u32;
            assert(total as nat == 5 * prev_total + stack@[j] as nat);
            pow5_proof(i - j - 1, i - j - 1);
            seq_drop_last_proof(stack, j);
        }
    }
    
    let result = total;
    
    proof {
        assert(result as nat == f2(n as nat)) by {
            let mut k: nat = i;
            let mut acc: nat = 0;
            let mut current_n: nat = n as nat;
            
            while k > 0
                invariant
                    0 <= k && k <= i,
                    current_n == (n as nat) / pow3(i - k),
                    acc == f2(current_n)
            {
                k = k - 1;
                let div = current_n / 3;
                let rem = current_n % 4;
                current_n = div;
                acc = 5 * f2(div) + rem;
            }
            assert(acc == f2(n as nat));
        };
    }
    
    result
}
// </vc-code>

fn main() {}

}