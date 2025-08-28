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
proof fn lemma_bull_equiv(s: Seq<nat>, u: Seq<nat>, i: nat)
    requires 
        s.len() == u.len(),
        i <= s.len()
    ensures
        reccbull(s, u, i as int) == count_bulls_from(s, u, i)
    decreases s.len() - i
{
    if i == s.len() {
        assert(reccbull(s, u, i as int) == 0);
        assert(count_bulls_from(s, u, i) == 0);
    } else {
        lemma_bull_equiv(s, u, i + 1);
    }
}

proof fn lemma_cow_equiv(s: Seq<nat>, u: Seq<nat>, i: nat)
    requires 
        s.len() == u.len(),
        i <= s.len()
    ensures
        recccow(s, u, i as int) == count_cows_from(s, u, i)
    decreases s.len() - i
{
    if i == s.len() {
        assert(recccow(s, u, i as int) == 0);
        assert(count_cows_from(s, u, i) == 0);
    } else {
        lemma_cow_equiv(s, u, i + 1);
    }
}

spec fn count_bulls_from(s: Seq<nat>, u: Seq<nat>, i: nat) -> nat
    decreases s.len() - i
{
    if i >= s.len() {
        0
    } else if s[i as int] == u[i as int] {
        count_bulls_from(s, u, i + 1) + 1
    } else {
        count_bulls_from(s, u, i + 1)
    }
}

spec fn count_cows_from(s: Seq<nat>, u: Seq<nat>, i: nat) -> nat
    decreases s.len() - i
{
    if i >= s.len() {
        0
    } else if s[i as int] != u[i as int] && s.contains(u[i as int]) {
        count_cows_from(s, u, i + 1) + 1
    } else {
        count_cows_from(s, u, i + 1)
    }
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    let mut bulls: u32 = 0;
    let mut cows: u32 = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s.len() == u.len(),
            bulls as nat == count_bulls_from(s@.map(|j, x: u32| x as nat), u@.map(|j, x: u32| x as nat), 0) - count_bulls_from(s@.map(|j, x: u32| x as nat), u@.map(|j, x: u32| x as nat), i as nat),
            cows as nat == count_cows_from(s@.map(|j, x: u32| x as nat), u@.map(|j, x: u32| x as nat), 0) - count_cows_from(s@.map(|j, x: u32| x as nat), u@.map(|j, x: u32| x as nat), i as nat)
    {
        if s[i] == u[i] {
            bulls = bulls + 1;
        } else {
            let mut found = false;
            let mut j = 0;
            while j < s.len() && !found
                invariant
                    0 <= j <= s.len(),
                    found ==> s@.contains(u[i] as nat),
                    !found ==> forall|k: int| 0 <= k < j ==> s@[k] != u[i] as nat
            {
                if s[j] == u[i] {
                    found = true;
                }
                j = j + 1;
            }
            if found {
                cows = cows + 1;
            }
        }
        i = i + 1;
    }
    
    proof {
        let s_nat = s@.map(|j, x: u32| x as nat);
        let u_nat = u@.map(|j, x: u32| x as nat);
        lemma_bull_equiv(s_nat, u_nat, 0);
        lemma_cow_equiv(s_nat, u_nat, 0);
        assert(bulls as nat == bullspec(s_nat, u_nat));
        assert(cows as nat == cowspec(s_nat, u_nat));
    }
    
    (bulls, cows)
}
// </vc-code>

fn main() {}

}