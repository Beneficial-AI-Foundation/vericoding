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
proof fn lemma_reccbull_step(s: Seq<nat>, u: Seq<nat>, i: int)
    requires
        0 <= i < s.len(),
        s.len() == u.len()
    ensures
        if s[i] == u[i] {
            reccbull(s, u, i) == reccbull(s, u, i + 1) + 1
        } else {
            reccbull(s, u, i) == reccbull(s, u, i + 1)
        }
{
    assert(0 <= i <= s.len() == u.len());
    if s[i] == u[i] {
        assert(reccbull(s, u, i) == reccbull(s, u, i + 1) + 1);
    } else {
        assert(reccbull(s, u, i) == reccbull(s, u, i + 1));
    }
}

proof fn lemma_recccow_step(s: Seq<nat>, u: Seq<nat>, i: int)
    requires
        0 <= i < s.len(),
        s.len() == u.len()
    ensures
        if s[i] != u[i] && s.contains(u[i]) {
            recccow(s, u, i) == recccow(s, u, i + 1) + 1
        } else {
            recccow(s, u, i) == recccow(s, u, i + 1)
        }
{
    assert(0 <= i <= s.len() == u.len());
    if s[i] != u[i] && s.contains(u[i]) {
        assert(recccow(s, u, i) == recccow(s, u, i + 1) + 1);
    } else {
        assert(recccow(s, u, i) == recccow(s, u, i + 1));
    }
}

fn contains_vec_u32(s: &Vec<u32>, val: u32) -> (res: bool)
    ensures
        res == (s@.map(|i, x: u32| x as nat)).contains(val as nat)
{
    let mut j: usize = 0;
    let mut found: bool = false;

    while j < s.len()
        invariant 0 <= j <= s.len()
        invariant
            found == (exists|k: int|
                0 <= k < j &&
                #[trigger] (s@.map(|i, x: u32| x as nat))[k] == val as nat)
    {
        if s[j] == val {
            found = true;
            proof {
                let jj = j as int;
                assert(0 <= jj < s@.len());
                assert((s@.map(|i, x: u32| x as nat))[jj] == s@[jj] as nat);
                assert((s@.map(|i, x: u32| x as nat))[jj] == val as nat);
            }
        }
        j = j + 1;
    }

    proof {
        // At end of loop: j == s.len()
        assert(j == s.len());
        assert(found == (exists|k: int|
            0 <= k < s.len() &&
            #[trigger] (s@.map(|i, x: u32| x as nat))[k] == val as nat));
        assert((s@.map(|i, x: u32| x as nat)).contains(val as nat) == (exists|k: int|
            0 <= k < s.len() &&
            #[trigger] (s@.map(|i, x: u32| x as nat))[k] == val as nat));
    }

    found
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
    let mut bulls: u32 = 0u32;
    let mut cows: u32 = 0u32;
    let mut i: usize = 0;

    while i < n
        invariant 0 <= i <= n
        invariant bulls as nat + reccbull(s@.map(|j, x: u32| x as nat), u@.map(|j, x: u32| x as nat), i as int)
                 == reccbull(s@.map(|j, x: u32| x as nat), u@.map(|j, x: u32| x as nat), 0)
        invariant cows as nat + recccow(s@.map(|j, x: u32| x as nat), u@.map(|j, x: u32| x as nat), i as int)
                 == recccow(s@.map(|j, x: u32| x as nat), u@.map(|j, x: u32| x as nat), 0)
        invariant s@.len() == u@.len()
    {
        let si = s[i];
        let ui0 = u[i];

        proof {
            let ii = i as int;
            assert(0 <= ii < s@.len());
            assert(s@.len() == u@.len());
            assert((s@.map(|j, x: u32| x as nat))[ii] == s@[ii] as nat);
            assert((u@.map(|j, x: u32| x as nat))[ii] == u@[ii] as nat);
        }

        if si == ui0 {
            proof {
                let ii = i as int;
                let ss = s@.map(|j, x: u32| x as nat);
                let uu = u@.map(|j, x: u32| x as nat);
                assert(ss.len() == uu.len());
                assert(0 <= ii < ss.len());
                assert(ss[ii] == uu[ii]);
                lemma_reccbull_step(ss, uu, ii);
                assert(reccbull(ss, uu, ii) == reccbull(ss, uu, ii + 1) + 1);
            }
            bulls = bulls + 1;
        } else {
            let found = contains_vec_u32(&s, ui0);
            proof {
                let ii = i as int;
                let ss = s@.map(|j, x: u32| x as nat);
                let uu = u@.map(|j, x: u32| x as nat);
                assert(ss.len() == uu.len());
                assert(0 <= ii < ss.len());
                assert(ss[ii] != uu[ii]);
                lemma_recccow_step(ss, uu, ii);
                if found {
                    assert(ss.contains(uu[ii]));
                    assert(recccow(ss, uu, ii) == recccow(ss, uu, ii + 1) + 1);
                } else {
                    assert(!ss.contains(uu[ii]));
                    assert(recccow(ss, uu, ii) == recccow(ss, uu, ii + 1));
                }
            }
            if found {
                cows = cows + 1;
            }
        }

        proof {
            let ii = i as int;
            let ss = s@.map(|j, x: u32| x as nat);
            let uu = u@.map(|j, x: u32| x as nat);
            assert(ss.len() == uu.len());
            assert(0 <= ii < ss.len());
            if (s[i] == u[i]) {
                lemma_reccbull_step(ss, uu, ii);
                assert(reccbull(ss, uu, ii) == reccbull(ss, uu, ii + 1) + 1);
            } else {
                lemma_reccbull_step(ss, uu, ii);
                assert(reccbull(ss, uu, ii) == reccbull(ss, uu, ii + 1));
            }
            if (s[i] != u[i]) {
                lemma_recccow_step(ss, uu, ii);
                if contains_vec_u32(&s, u[i]) {
                    assert(ss.contains(uu[ii]));
                    assert(recccow(ss, uu, ii) == recccow(ss, uu, ii + 1) + 1);
                } else {
                    assert(!ss.contains(uu[ii]));
                    assert(recccow(ss, uu, ii) == recccow(ss, uu, ii + 1));
                }
            } else {
                lemma_recccow_step(ss, uu, ii);
                assert(recccow(ss, uu, ii) == recccow(ss, uu, ii + 1));
            }
        }

        i = i + 1;
    }

    proof {
        let ss = s@.map(|j, x: u32| x as nat);
        let uu = u@.map(|j, x: u32| x as nat);
        assert(ss.len() == uu.len());
        assert(0 <= ss.len() <= ss.len() == uu.len());
        assert(reccbull(ss, uu, ss.len()) == 0);
        assert(recccow(ss, uu, ss.len()) == 0);
        assert(bulls as nat + reccbull(ss, uu, ss.len() as int) == reccbull(ss, uu, 0));
        assert(cows as nat + recccow(ss, uu, ss.len() as int) == recccow(ss, uu, 0));
        assert(bulls as nat == recc
// </vc-code>

fn main() {}

}