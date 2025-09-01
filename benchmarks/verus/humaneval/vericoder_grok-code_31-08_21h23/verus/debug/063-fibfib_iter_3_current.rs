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
proof fn lemma_fibfib_def(n: nat)
    requires n >= 3,
    ensures spec_fibfib(n as nat) == spec_fibfib((n - 1) as nat) + spec_fibfib((n - 2) as nat) + spec_fibfib((n - 3) as nat),
{
    // Proof is by definition: spec_fibfib unwrathes to the sum for n >= 3
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
    let mut v: Vec<u32> = vec![0, 0, 1];
    proof {
        assert(v@[0] == spec_fibfib(0));
        assert(v@[1] == spec_fibfib(1));
        assert(v@[2] == spec_fibfib(2));
    }
    let mut i = 3u32;
    while i <= x
        decreases ((x as int) - (i as int))
        invariant
            v@.len() == i as int,
            forall |j: int| 0 <= j < i ==> v@[j] == spec_fibfib(j as nat)
    {
        proof {
            assert(i >= 3);
            assert(v@[((i - 3) as int)] == spec_fibfib(((i - 3) as nat)));
            assert(v@[((i - 2) as int)] == spec_fibfib(((i - 2) as nat)));
            assert(v@[((i - 1) as int)] == spec_fibfib(((i - 1) as nat)));
        }
        let temp = v[(i - 3) as usize].checked_add(v[(i - 2) as usize]);
        let next_opt = match temp {
            Some(sum) => sum.checked_add(v[(i - 1) as usize]),
            None => None,
        };
        if let Some(sum) = next_opt {
            v.push(sum);
            proof {
                lemma_fibfib_def(i as nat);
                assert(v@[v.len() - 1] == spec_fibfib(i as nat));
            }
        } else {
            return None;
        }
        i = i + 1;
    }
    Some(v[x as usize])
}
// </vc-code>

fn main() {}
}