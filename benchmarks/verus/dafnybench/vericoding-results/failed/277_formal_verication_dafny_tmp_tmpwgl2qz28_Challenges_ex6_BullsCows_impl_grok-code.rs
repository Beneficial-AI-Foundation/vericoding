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
spec fn reccbull_nat(s: Seq<nat>, u: Seq<nat>, i: int) -> nat
    decreases s.len() - i
{
    if !(0 <= i <= s.len() == u.len()) {
        arbitrary()
    } else if i == s.len() {
        0
    } else if s.index(i) == u.index(i) {
        reccbull_nat(s, u, i + 1) + 1
    } else {
        reccbull_nat(s, u, i + 1)
    }
}

spec fn recccow_nat(s: Seq<nat>, u: Seq<nat>, i: int) -> nat
    decreases s.len() - i
{
    if !(0 <= i <= s.len() == u.len()) {
        arbitrary()
    } else if i == s.len() {
        0
    } else if s.index(i) != u.index(i) && s.contains(u.index(i)) {
        recccow_nat(s, u, i + 1) + 1
    } else {
        recccow_nat(s, u, i + 1)
    }
}

#[verifier(opaque)]
spec fn bullspec_nat(s: Seq<nat>, u: Seq<nat>) -> nat {
    if !(0 <= u.len() == s.len() && nomultiples(u)) {
        arbitrary()
    } else {
        reccbull_nat(s, u, 0)
    }
}

#[verifier(opaque)]
spec fn cowspec_nat(s: Seq<nat>, u: Seq<nat>) -> nat {
    if !(0 <= u.len() == s.len() && nomultiples(u)) {
        arbitrary()
    } else {
        recccow_nat(s, u, 0)
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
    let mut bull = 0u32;
    let mut cow = 0u32;
    let len = s.len();
    let s_nat: Ghost<Seq<nat>> = Ghost(s@.map(|i: int, x: u32| x as nat));
    let u_nat: Ghost<Seq<nat>> = Ghost(u@.map(|i: int, x: u32| x as nat));

    proof {
        assert(bullspec_nat(s_nat@, u_nat@) == reccbull_nat(s_nat@, u_nat@, 0));
        assert(cowspec_nat(s_nat@, u_nat@) == recccow_nat(s_nat@, u_nat@, 0));
        assert(bullspec_nat(s@.map(|i, x: u32| x as nat), u@.map(|i, x: u32| x as nat)) == bullspec_nat(s_nat@, u_nat@));
        assert(cowspec_nat(s@.map(|i, x: u32| x as nat), u@.map(|i, x: u32| x as nat)) == cowspec_nat(s_nat@, u_nat@));
    }

    let mut i = 0usize;
    while i < len
        invariant
            i as nat <= len as nat,
            bull as nat == #[trigger] bullspec_nat(s_nat@, u_nat@) - reccbull_nat(s_nat@, u_nat@, i as int),
            cow as nat == #[trigger] cowspec_nat(s_nat@, u_nat@) - recccow_nat(s_nat@, u_nat@, i as int),
            s_nat@ == s@.map(|i, x: u32| x as nat),
            u_nat@ == u@.map(|i, x: u32| x as nat),
            nomultiples(s_nat@),
            nomultiples(u_nat@),
    {
        let target: u32 = u[i];
        if s[i] == target {
            bull = bull + 1;
            proof {
                assert(reccbull_nat(s_nat@, u_nat@, i as int + 1) + 1 == reccbull_nat(s_nat@, u_nat@, i as int));
            }
        } else {
            let mut found = false;
            let mut j = 0usize;
            while j < len
                invariant
                    j as nat <= len as nat,
                    if found {
                        exists |k: usize| #[trigger] (k < j) && s@[k as int] == target
                    } else {
                        forall |k: usize| #[trigger] (k < j) ==> s@[k as int] != target
                    },
                    s_nat@ == s@.map(|i, x: u32| x as nat),
                    u_nat@ == u@.map(|i, x: u32| x as nat),
                    u@[i as int] == target,
                    (j > 0) ==> (forall |k: usize| k < j ==> s@[k as int] == s_nat@.index(k as int) as u32),
                    target == u_nat@.index(i as int) as u32,
            {
                let curr: u32 = s[j];
                if curr == target {
                    found = true;
                }
                proof {
                    if found {
                        // trigger the exists
                    } else {
                        assert(forall |k: usize| k <= j ==> s@[k as int] != target);
                    }
                }
                j = j + 1;
            }
            if found {
                cow = cow + 1;
                proof {
                    assert(recccow_nat(s_nat@, u_nat@, i as int + 1) + 1 == recccow_nat(s_nat@, u_nat@, i as int));
                    assert(s@[i as int] == s_nat@.index(i as int) as u32);
                }
            } else {
                proof {
                    assert(recccow_nat(s_nat@, u_nat@, i as int + 1) == recccow_nat(s_nat@, u_nat@, i as int));
                }
            }
        }
        i = i + 1;

        proof {
            assert(bull as nat == bullspec_nat(s_nat@, u_nat@) - reccbull_nat(s_nat@, u_nat@, i as int));
            assert(cow as nat == cowspec_nat(s_nat@, u_nat@) - recccow_nat(s_nat@, u_nat@, i as int));
        }
    }

    proof {
        assert(reccbull_nat(s_nat@, u_nat@, len as int) == 0);
        assert(recccow_nat(s_nat@, u_nat@, len as int) == 0);
        assert(bull as nat == bullspec_nat(s_nat@, u_nat@));
        assert(cow as nat == cowspec_nat(s_nat@, u_nat@));
    }

    (bull, cow)
}
// </vc-code>

fn main() {}

}