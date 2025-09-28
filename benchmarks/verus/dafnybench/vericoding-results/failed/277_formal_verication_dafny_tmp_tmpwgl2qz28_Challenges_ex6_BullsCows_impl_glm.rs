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
spec fn reccbull_iter(s: Seq<nat>, u: Seq<nat>, i: int, acc: nat) -> nat
    decreases s.len() - i
{
    if !(0 <= i <= s.len() == u.len()) {
        arbitrary()
    } else if i == s.len() {
        acc
    } else if s[i] == u[i] {
        reccbull_iter(s, u, i + 1, acc + 1)
    } else {
        reccbull_iter(s, u, i + 1, acc)
    }
}

proof fn lemma_reccbull_equiv(s: Seq<nat>, u: Seq<nat>, i: int)
    requires
        0 <= i <= s.len() == u.len(),
        nomultiples(u),
    ensures
        reccbull(s, u, i) == reccbull_iter(s, u, i, 0)
{
    if i == s.len() {
    } else {
        lemma_reccbull_equiv(s, u, i + 1);
        if s[i] == u[i] {
            assert(reccbull(s, u, i) == reccbull_iter(s, u, i, 0));
        } else {
            assert(reccbull(s, u, i) == reccbull_iter(s, u, i, 0));
        }
    }
}

spec fn recccow_iter(s: Seq<nat>, u: Seq<nat>, i: int, acc: nat) -> nat
    decreases s.len() - i
{
    if !(0 <= i <= s.len() == u.len()) {
        arbitrary()
    } else if i == s.len() {
        acc
    } else if s[i] != u[i] && s.contains(u[i]) {
        recccow_iter(s, u, i + 1, acc + 1)
    } else {
        recccow_iter(s, u, i + 1, acc)
    }
}

proof fn lemma_recccow_equiv(s: Seq<nat>, u: Seq<nat>, i: int)
    requires
        0 <= i <= s.len() == u.len(),
        nomultiples(u),
    ensures
        recccow(s, u, i) == recccow_iter(s, u, i, 0)
{
    if i == s.len() {
    } else {
        lemma_recccow_equiv(s, u, i + 1);
        if s[i] != u[i] && s.contains(u[i]) {
            assert(recccow(s, u, i) == recccow_iter(s, u, i, 0));
        } else {
            assert(recccow(s, u, i) == recccow_iter(s, u, i, 0));
        }
    }
}

proof fn lemma_bulls_cows_disjoint_count(s: Seq<nat>, u: Seq<nat>)
    requires
        0 < s.len() == u.len(),
        nomultiples(u),
    ensures
        bullspec(s, u) + cowspec(s, u) <= s.len()
{
    lemma_reccbull_equiv(s, u, 0);
    lemma_recccow_equiv(s, u, 0);
    let n = s.len();
    assert forall|i: int| 0 <= i < n implies
        ((s[i] == u[i]) && (s[i] != u[i] && s.contains(u[i])) == false) by {
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
    let n = s.len();
    let mut bulls: u32 = 0;
    let mut cows: u32 = 0;
    let mut i = 0;

    while i < n
        invariant 
            0 <= i <= n,
            bulls as nat == reccbull_iter(s@.map(|x| x as nat), u@.map(|x| x as nat), i as int, 0),
            cows as nat == recccow_iter(s@.map(|x| x as nat), u@.map(|x| x as nat), i as int, 0),
    {
        if s[i] == u[i] {
            bulls = bulls + 1;
        } else {
            let u_i = u[i];
            let mut j = 0;
            let mut found = false;
            while j < i
                invariant 
                    0 <= j <= i,
                    found ==> exists|k: usize| 0 <= k < j && s@[k] == u_i,
                    !found ==> forall|k: usize| 0 <= k < j ==> s@[k] != u_i,
            {
                if !found && s[j] == u_i {
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
        lemma_reccbull_equiv(s@.map(|x| x as nat), u@.map(|x| x as nat), 0);
        lemma_recccow_equiv(s@.map(|x| x as nat), u@.map(|x| x as nat), 0);
    }

    (bulls, cows)
}
// </vc-code>

fn main() {}

}