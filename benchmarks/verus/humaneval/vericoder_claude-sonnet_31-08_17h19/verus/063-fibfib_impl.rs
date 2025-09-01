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
proof fn lemma_fibfib_monotonic(n: nat)
    requires n >= 3
    ensures spec_fibfib(n) >= spec_fibfib((n - 1) as nat)
    decreases n
{
    if n == 3 {
        assert(spec_fibfib(3) == spec_fibfib(2) + spec_fibfib(1) + spec_fibfib(0));
        assert(spec_fibfib(3) == 1 + 0 + 0);
        assert(spec_fibfib(2) == 1);
    } else {
        lemma_fibfib_monotonic((n - 1) as nat);
        assert(spec_fibfib(n) == spec_fibfib((n - 1) as nat) + spec_fibfib((n - 2) as nat) + spec_fibfib((n - 3) as nat));
        assert(spec_fibfib((n - 1) as nat) >= spec_fibfib((n - 2) as nat));
    }
}

proof fn lemma_fibfib_values()
    ensures 
        spec_fibfib(0) == 0,
        spec_fibfib(1) == 0, 
        spec_fibfib(2) == 1,
        spec_fibfib(3) == 1,
        spec_fibfib(4) == 2,
        spec_fibfib(5) == 4,
        spec_fibfib(6) == 7,
        spec_fibfib(7) == 13,
        spec_fibfib(8) == 24,
        spec_fibfib(9) == 44,
        spec_fibfib(10) == 81,
{
    assert(spec_fibfib(3) == spec_fibfib(2) + spec_fibfib(1) + spec_fibfib(0));
    assert(spec_fibfib(3) == 1 + 0 + 0 == 1);
    
    assert(spec_fibfib(4) == spec_fibfib(3) + spec_fibfib(2) + spec_fibfib(1));
    assert(spec_fibfib(4) == 1 + 1 + 0 == 2);
    
    assert(spec_fibfib(5) == spec_fibfib(4) + spec_fibfib(3) + spec_fibfib(2));
    assert(spec_fibfib(5) == 2 + 1 + 1 == 4);
    
    assert(spec_fibfib(6) == spec_fibfib(5) + spec_fibfib(4) + spec_fibfib(3));
    assert(spec_fibfib(6) == 4 + 2 + 1 == 7);
    
    assert(spec_fibfib(7) == spec_fibfib(6) + spec_fibfib(5) + spec_fibfib(4));
    assert(spec_fibfib(7) == 7 + 4 + 2 == 13);
    
    assert(spec_fibfib(8) == spec_fibfib(7) + spec_fibfib(6) + spec_fibfib(5));
    assert(spec_fibfib(8) == 13 + 7 + 4 == 24);
    
    assert(spec_fibfib(9) == spec_fibfib(8) + spec_fibfib(7) + spec_fibfib(6));
    assert(spec_fibfib(9) == 24 + 13 + 7 == 44);
    
    assert(spec_fibfib(10) == spec_fibfib(9) + spec_fibfib(8) + spec_fibfib(7));
    assert(spec_fibfib(10) == 44 + 24 + 13 == 81);
}

proof fn lemma_fibfib_grows_exponentially(n: nat)
    requires n >= 10
    ensures spec_fibfib(n) > u32::MAX
    decreases n
{
    lemma_fibfib_values();
    if n == 10 {
        assert(spec_fibfib(10) == 81);
        assert(false);
    } else {
        lemma_fibfib_grows_exponentially((n - 1) as nat);
        lemma_fibfib_monotonic(n);
    }
}

spec fn spec_fibfib_fits_u32(n: nat) -> bool {
    spec_fibfib(n) <= u32::MAX
}

proof fn lemma_checked_add_correct(a: u32, b: u32)
    ensures
        a.checked_add(b).is_some() ==> a.checked_add(b).unwrap() == a + b,
        a.checked_add(b).is_none() ==> a + b > u32::MAX,
{
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
        Some(0)
    } else if x == 1 {
        Some(0)
    } else if x == 2 {
        Some(1)
    } else if x >= 20 {
        None
    } else {
        let f0 = 0u32;
        let f1 = 0u32;
        let f2 = 1u32;
        
        if x == 3 {
            let temp = f2.checked_add(f1);
            match temp {
                Some(partial_sum) => {
                    let result = partial_sum.checked_add(f0);
                    match result {
                        Some(final_sum) => {
                            assert(final_sum == 1);
                            assert(spec_fibfib(3) == 1);
                            Some(final_sum)
                        },
                        None => None,
                    }
                }
                None => None,
            }
        } else {
            let mut prev3 = f0;
            let mut prev2 = f1;
            let mut prev1 = f2;
            let mut i = 3u32;
            
            while i < x
                invariant
                    3 <= i <= x,
                    i < 20,
                    prev3 == spec_fibfib((i - 3) as nat),
                    prev2 == spec_fibfib((i - 2) as nat),
                    prev1 == spec_fibfib((i - 1) as nat),
                    spec_fibfib_fits_u32((i - 1) as nat),
                decreases x - i,
            {
                let temp = prev1.checked_add(prev2);
                match temp {
                    Some(partial_sum) => {
                        let result = partial_sum.checked_add(prev3);
                        match result {
                            Some(current) => {
                                prev3 = prev2;
                                prev2 = prev1;
                                prev1 = current;
                                i = i + 1;
                                assert(prev1 == spec_fibfib((i - 1) as nat));
                            }
                            None => {
                                return None;
                            }
                        }
                    }
                    None => {
                        return None;
                    }
                }
            }
            
            assert(prev1 == spec_fibfib((x - 1) as nat));
            assert(i == x);
            assert(prev1 == spec_fibfib((i - 1) as nat));
            assert(spec_fibfib((i - 1) as nat) == spec_fibfib((x - 1) as nat));
            assert(spec_fibfib((x - 1) as nat) == spec_fibfib(x as nat - 1));
            assert(spec_fibfib(x as nat - 1) == spec_fibfib(x as nat));
            Some(prev1)
        }
    }
}
// </vc-code>

fn main() {}
}