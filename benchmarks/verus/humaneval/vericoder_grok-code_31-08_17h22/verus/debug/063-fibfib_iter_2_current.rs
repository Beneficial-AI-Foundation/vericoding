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
        let a = seq@[(i as int) - 3];
        let b = seq@[(i as int) - 2];
        let c = seq@[(i as int) - 1];
        let sum1 = a as u64 + b as u64;
        if sum1 > u32::MAX as u64 {
            return None;
        }
        let sum2 = sum1 + c as u64;
        if sum2 > u32::MAX as u64 {
            return None;
        }
        let next = sum2 as u32;
        assert(spec_fibfib(i as nat) == spec_fibfib((i - 1) as nat) + spec_fibfib((i - 2) as nat) + spec_fibfib((i - 3) as nat));
        assert(seq@[(i as int) - 1] as nat == spec_fibfib((i - 1) as nat));
        assert(seq@[(i as int) - 2] as nat == spec_fibfib((i - 2) as nat));
        assert(seq@[(i as int) - 3] as nat == spec_fibfib((i - 3) as nat));
        assert(next as nat == spec_fibfib(i as nat));
        seq.push(next);
        i += 1;
    }
    return Some(seq@[x as int]);
}
// </vc-code>

fn main() {}
}