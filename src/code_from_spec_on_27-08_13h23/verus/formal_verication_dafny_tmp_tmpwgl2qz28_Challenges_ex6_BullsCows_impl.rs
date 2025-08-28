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
spec fn seq_contains<T>(s: Seq<T>, value: T) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == value
}

proof fn lemma_reccbull_correct(s: Seq<nat>, u: Seq<nat>, i: int)
    requires
        0 <= i <= s.len(),
        s.len() == u.len(),
    ensures
        reccbull(s, u, i) == {
            let mut count = 0;
            let mut j = i;
            while j < s.len() {
                if s[j] == u[j] {
                    count = count + 1;
                }
                j = j + 1;
            }
            count
        },
    decreases s.len() - i
{
    if i == s.len() {
        assert(reccbull(s, u, i) == 0);
    } else {
        lemma_reccbull_correct(s, u, i + 1);
        if s[i] == u[i] {
            assert(reccbull(s, u, i) == reccbull(s, u, i + 1) + 1);
        } else {
            assert(reccbull(s, u, i) == reccbull(s, u, i + 1));
        }
    }
}

proof fn lemma_recccow_correct(s: Seq<nat>, u: Seq<nat>, i: int)
    requires
        0 <= i <= s.len(),
        s.len() == u.len(),
    ensures
        recccow(s, u, i) == {
            let mut count = 0;
            let mut j = i;
            while j < s.len() {
                if s[j] != u[j] && seq_contains(s, u[j]) {
                    count = count + 1;
                }
                j = j + 1;
            }
            count
        },
    decreases s.len() - i
{
    if i == s.len() {
        assert(recccow(s, u, i) == 0);
    } else {
        lemma_recccow_correct(s, u, i + 1);
        if s[i] != u[i] && seq_contains(s, u[i]) {
            assert(recccow(s, u, i) == recccow(s, u, i + 1) + 1);
        } else {
            assert(recccow(s, u, i) == recccow(s, u, i + 1));
        }
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
fn BullsCows(s: Vec<u32>, u: Vec<u32>) -> (ret: (u32, u32))
    requires 
        0 < u.len() == s.len() <= 10,
        nomultiples(s@.map(|i, x: u32| x as nat)) && nomultiples(u@.map(|i, x: u32| x as nat))
    ensures 
        ret.0 >= 0 && ret.1 >= 0,
        ret.0 as nat == bullspec(s@.map(|i, x: u32| x as nat), u@.map(|i, x: u32| x as nat)),
        ret.1 as nat == cowspec(s@.map(|i, x: u32| x as nat), u@.map(|i, x: u32| x as nat))
{
    let s_nat = s@.map(|i, x: u32| x as nat);
    let u_nat = u@.map(|i, x: u32| x as nat);
    let mut bulls: u32 = 0;
    let mut cows: u32 = 0;
    let mut i: usize = 0;

    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s.len() == u.len(),
            bulls as nat == reccbull(s_nat, u_nat, 0) - reccbull(s_nat, u_nat, i as int),
            cows as nat == recccow(s_nat, u_nat, 0) - recccow(s_nat, u_nat, i as int)
    {
        if s[i] == u[i] {
            bulls = bulls + 1;
        } else {
            let mut j: usize = 0;
            let mut found = false;
            while j < s.len()
                invariant
                    0 <= j <= s.len(),
                    !found ==> forall|k: usize| 0 <= k < j ==> s[k] != u[i]
            {
                if s[j] == u[i] {
                    found = true;
                    break;
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
        lemma_reccbull_correct(s_nat, u_nat, 0);
        lemma_recccow_correct(s_nat, u_nat, 0);
    }

    (bulls, cows)
}
// </vc-code>

fn main() {}

}