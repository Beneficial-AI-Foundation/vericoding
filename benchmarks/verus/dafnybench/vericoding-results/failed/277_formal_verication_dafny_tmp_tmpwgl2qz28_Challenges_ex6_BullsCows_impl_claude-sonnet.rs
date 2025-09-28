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
spec fn contains_u32(s: &Vec<u32>, val: u32) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == val
}

proof fn lemma_reccbull_correct(s: Seq<nat>, u: Seq<nat>, i: int, bulls: nat)
    requires 
        0 <= i <= s.len() == u.len(),
        bulls == reccbull(s, u, i)
    ensures
        bulls == reccbull(s, u, i)
    decreases s.len() - i
{
}

proof fn lemma_recccow_correct(s: Seq<nat>, u: Seq<nat>, i: int, cows: nat)
    requires 
        0 <= i <= s.len() == u.len(),
        cows == recccow(s, u, i)
    ensures
        cows == recccow(s, u, i)
    decreases s.len() - i
{
}

proof fn lemma_contains_equiv(s: &Vec<u32>, val: u32)
    ensures
        contains_u32(s, val) <==> s@.map(|i, x: u32| x as nat).contains(val as nat)
{
    let s_nat = s@.map(|i, x: u32| x as nat);
    
    if contains_u32(s, val) {
        let i = choose|i: int| 0 <= i < s.len() && s[i] == val;
        assert(s_nat[i] == val as nat);
        assert(s_nat.contains(val as nat));
    }
    
    if s_nat.contains(val as nat) {
        let i = choose|i: int| 0 <= i < s_nat.len() && s_nat[i] == val as nat;
        assert(s[i] == val);
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
    let mut bulls: u32 = 0;
    let mut cows: u32 = 0;
    
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s.len() == u.len(),
            bulls <= 10,
            cows <= 10,
            bulls as nat == reccbull(s@.map(|i, x: u32| x as nat), u@.map(|i, x: u32| x as nat), 0) - reccbull(s@.map(|i, x: u32| x as nat), u@.map(|i, x: u32| x as nat), i as int),
            cows as nat == recccow(s@.map(|i, x: u32| x as nat), u@.map(|i, x: u32| x as nat), 0) - recccow(s@.map(|i, x: u32| x as nat), u@.map(|i, x: u32| x as nat), i as int)
        decreases s.len() - i
    {
        if s[i] == u[i] {
            assert(bulls < 10);
            bulls = bulls + 1;
        } else {
            let mut j = 0;
            let mut found = false;
            while j < s.len()
                invariant
                    0 <= j <= s.len(),
                    0 <= i < s.len(),
                    i < u.len(),
                    found ==> exists|k: int| 0 <= k < j && s@[k] == u@[i as int],
                    !found ==> forall|k: int| 0 <= k < j ==> s@[k] != u@[i as int]
                decreases s.len() - j
            {
                if s[j] == u[i] {
                    found = true;
                    break;
                }
                j = j + 1;
            }
            if found {
                assert(cows < 10);
                cows = cows + 1;
            }
        }
        i = i + 1;
    }
    
    (bulls, cows)
}
// </vc-code>

fn main() {}

}