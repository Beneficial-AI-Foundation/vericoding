use vstd::prelude::*;

verus! {

// see pdf 'ex6 & 7 documentation' for excercise question

spec fn bullspec(s: Seq<nat>, u: Seq<nat>) -> nat {
    if !(0 <= u.len() == s.len() && nomultiples(u)) {
        arbitrary()
    } else {
        reccbull(s, u, 0)
    }
}

spec fn cowspec(s: Seq<nat>, u: Seq<nat>) -> nat {
    if !(0 <= u.len() == s.len() && nomultiples(u)) {
        arbitrary()
    } else {
        recccow(s, u, 0)
    }
}

spec fn reccbull(s: Seq<nat>, u: Seq<nat>, i: int) -> nat
    decreases s.len() - i
{
    if !(0 <= i <= s.len() == u.len()) {
        arbitrary()
    } else if i == s.len() {
        0
    } else if s[i] == u[i] {
        reccbull(s, u, i + 1) + 1
    } else {
        reccbull(s, u, i + 1)
    }
}

spec fn recccow(s: Seq<nat>, u: Seq<nat>, i: int) -> nat
    decreases s.len() - i
{
    if !(0 <= i <= s.len() == u.len()) {
        arbitrary()
    } else if i == s.len() {
        0
    } else if s[i] != u[i] && s.contains(u[i]) {
        recccow(s, u, i + 1) + 1
    } else {
        recccow(s, u, i + 1)
    }
}

spec fn nomultiples(u: Seq<nat>) -> bool {
    forall|j: int, k: int| 0 <= j < k < u.len() ==> u[j] != u[k]
}

// <vc-helpers>
proof fn lemma_bull_step(s: Seq<nat>, u: Seq<nat>, i: nat, bulls: nat)
    requires
        0 <= i < s.len() == u.len(),
        nomultiples(u),
        bulls == reccbull(s, u, 0) - reccbull(s, u, i as int),
    ensures
        if s[i as int] == u[i as int] {
            bulls + 1 == reccbull(s, u, 0) - reccbull(s, u, (i + 1) as int)
        } else {
            bulls == reccbull(s, u, 0) - reccbull(s, u, (i + 1) as int)
        }
{
    assert(reccbull(s, u, i as int) == if s[i as int] == u[i as int] {
        reccbull(s, u, (i + 1) as int) + 1
    } else {
        reccbull(s, u, (i + 1) as int)
    });
}

proof fn lemma_cow_step(s: Seq<nat>, u: Seq<nat>, i: nat, cows: nat)
    requires
        0 <= i < s.len() == u.len(),
        nomultiples(u),
        cows == recccow(s, u, 0) - recccow(s, u, i as int),
    ensures
        if s[i as int] != u[i as int] && s.contains(u[i as int]) {
            cows + 1 == recccow(s, u, 0) - recccow(s, u, (i + 1) as int)
        } else {
            cows == recccow(s, u, 0) - recccow(s, u, (i + 1) as int)
        }
{
    assert(recccow(s, u, i as int) == if s[i as int] != u[i as int] && s.contains(u[i as int]) {
        recccow(s, u, (i + 1) as int) + 1
    } else {
        recccow(s, u, (i + 1) as int)
    });
}

proof fn lemma_bull_base(s: Seq<nat>, u: Seq<nat>)
    requires
        0 <= s.len() == u.len(),
        nomultiples(u),
    ensures
        reccbull(s, u, s.len() as int) == 0,
{
}

proof fn lemma_cow_base(s: Seq<nat>, u: Seq<nat>)
    requires
        0 <= s.len() == u.len(),
        nomultiples(u),
    ensures
        recccow(s, u, s.len() as int) == 0,
{
}

spec fn contains_u32(s: Seq<u32>, val: u32) -> bool {
    exists|j: int| #[trigger] s[j] == val && 0 <= j < s.len()
}

proof fn lemma_contains_map(s: Seq<u32>, val: u32)
    ensures
        contains_u32(s, val) == s.map(|i, x: u32| x as nat).contains(val as nat),
{
    if contains_u32(s, val) {
        let j = choose|j: int| #[trigger] s[j] == val && 0 <= j < s.len();
        assert(s.map(|i, x: u32| x as nat)[j] == val as nat);
        assert(s.map(|i, x: u32| x as nat).contains(val as nat));
    }
    if s.map(|i, x: u32| x as nat).contains(val as nat) {
        let j = choose|j: int| #[trigger] s.map(|i, x: u32| x as nat)[j] == val as nat && 0 <= j < s.map(|i, x: u32| x as nat).len();
        assert(s[j] == val);
        assert(contains_u32(s, val));
    }
}
// </vc-helpers>

// <vc-spec>
fn BullsCows(s: Vec<u32>, u: Vec<u32>) -> (ret: (u32, u32))
    requires 
        0 < u.len() == s.len() <= 10,
        nomultiples(s@.map(|i, x: u32| x as nat)) && nomultiples(u@.map(|i, x: u32| x as nat))
    ensures 
        ret.0 >= 0 && ret.1 >= 0,
        ret.0 as nat == bullspec(s@.map(|i, x: u32| x as nat), u@.map(|i, x: u32| x as nat)),
        ret.1 as nat == cowspec(s@.map(|i, x: u32| x as nat), u@.map(|i, x: u32| x as nat))
// </vc-spec>
// <vc-code>
{
    let ghost s_nat = s@.map(|i, x: u32| x as nat);
    let ghost u_nat = u@.map(|i, x: u32| x as nat);
    
    let mut bulls: u32 = 0;
    let mut cows: u32 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s.len() == u.len(),
            bulls as nat == reccbull(s_nat, u_nat, 0) - reccbull(s_nat, u_nat, i as int),
            cows as nat == recccow(s_nat, u_nat, 0) - recccow(s_nat, u_nat, i as int),
            nomultiples(s_nat),
            nomultiples(u_nat),
            s_nat == s@.map(|j, x: u32| x as nat),
            u_nat == u@.map(|j, x: u32| x as nat),
        decreases s.len() - i
    {
        proof {
            assert(s_nat[i as int] == s[i as int] as nat);
            assert(u_nat[i as int] == u[i as int] as nat);
        }
        
        if s[i] == u[i] {
            proof {
                lemma_bull_step(s_nat, u_nat, i as nat, bulls as nat);
            }
            bulls = bulls + 1;
        } else {
            proof {
                lemma_bull_step(s_nat, u_nat, i as nat, bulls as nat);
            }
            
            // Check if u[i] is in s
            let mut found = false;
            let mut j: usize = 0;
            while j < s.len()
                invariant
                    0 <= j <= s.len(),
                    found == exists|k: int| 0 <= k < j as int && s[k as int] == u[i as int],
                decreases s.len() - j
            {
                if s[j] == u[i] {
                    found = true;
                    break;
                }
                j = j + 1;
            }
            
            if found {
                proof {
                    lemma_contains_map(s@, u[i as int]);
                    assert(s_nat.contains(u[i as int] as nat));
                    lemma_cow_step(s_nat, u_nat, i as nat, cows as nat);
                }
                cows = cows + 1;
            } else {
                proof {
                    lemma_contains_map(s@, u[i as int]);
                    assert(!s_nat.contains(u[i as int] as nat));
                    lemma_cow_step(s_nat, u_nat, i as nat, cows as nat);
                }
            }
        }
        
        i = i + 1;
    }
    
    proof {
        lemma_bull_base(s_nat, u_nat);
        lemma_cow_base(s_nat, u_nat);
        assert(bulls as nat == reccbull(s_nat, u_nat, 0));
        assert(cows as nat == recccow(s_nat, u_nat, 0));
        assert(bulls as nat == bullspec(s_nat, u_nat));
        assert(cows as nat == cowspec(s_nat, u_nat));
    }
    
    (bulls, cows)
}
// </vc-code>

fn main() {}

}