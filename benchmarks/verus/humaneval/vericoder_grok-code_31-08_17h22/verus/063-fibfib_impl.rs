use vstd::prelude::*;

verus! {

spec fn spec_fibfib(n: nat) -> (ret: nat)
    decreases n,
{
    if (n == 0) {
        0
    } else if (n == 1) {
        0
    } else if (n == 2) {
        1
    } else {
        spec_fibfib((n - 1) as nat) + spec_fibfib((n - 2) as nat) + spec_fibfib((n - 3) as nat)
    }
}
// pure-end

// <vc-helpers>
#[verifier(stack_limit=100)]
proof fn lemma_fibfib_correct(n: nat)
    decreases n,
    ensures
        spec_fibfib(n) == if n == 0 { 0 } else if n == 1 { 0 } else if n == 2 { 1 } else { spec_fibfib((n - 1) as nat) + spec_fibfib((n - 2) as nat) + spec_fibfib((n - 3) as nat) },
{
    if n > 2 {
        lemma_fibfib_correct((n - 1) as nat);
        lemma_fibfib_correct((n - 2) as nat);
        lemma_fibfib_correct((n - 3) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn fibfib(x: u32) -> (ret: Option<u32>)
    // post-conditions-start
    ensures
        ret.is_some() ==> spec_fibfib(x as nat) == ret.unwrap(),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if x == 0 {
        return Some(0);
    }
    if x == 1 {
        return Some(0);
    }
    if x == 2 {
        return Some(1);
    }
    let mut seq: Vec<u32> = Vec::new();
    seq.push(0);
    seq.push(0);
    seq.push(1);
    let mut i: u32 = 3;
    while i <= x
        invariant
            seq@.len() == i as int,
            forall |k: int| 0 <= k < i as int ==> #[trigger] spec_fibfib(k as nat) == seq@[k] as nat,
        decreases (x - i) as int,
    {
        proof {
            assert(i >= 3);
            assert(0 <= i as int - 1 < i as int);
            assert(0 <= i as int - 2 < i as int);
            assert(0 <= i as int - 3 < i as int);
        }
        let idx3: usize = ((i as int) - 3) as usize;
        let idx2: usize = ((i as int) - 2) as usize;
        let idx1: usize = ((i as int) - 1) as usize;
        let a = seq[idx3];
        let b = seq[idx2];
        let c = seq[idx1];
        let sum1 = a as u64 + b as u64;
        if sum1 > u32::MAX as u64 {
            return None;
        }
        let sum2 = sum1 + c as u64;
        if sum2 > u32::MAX as u64 {
            return None;
        }
        let next = sum2 as u32;
        proof {
            lemma_fibfib_correct(i as nat);
        }
        seq.push(next);
        i += 1;
    }
    return Some(seq[x as usize]);
}
// </vc-code>

fn main() {}
}