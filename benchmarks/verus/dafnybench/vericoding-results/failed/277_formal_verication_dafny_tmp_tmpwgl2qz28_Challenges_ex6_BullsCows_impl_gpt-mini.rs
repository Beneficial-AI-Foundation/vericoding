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
// <vc-helpers>
/* Updated helpers: none needed beyond standard library for this fix. */
// </vc-helpers>
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
    let n_usize: usize = s.len();
    let n: int = n_usize as int;
    let sseq = s@.map(|_, x: u32| x as nat);
    let useq = u@.map(|_, x: u32| x as nat);

    let mut i: int = 0;
    let mut bulls: u32 = 0;
    let mut cows: u32 = 0;

    while i < n
        invariant 0 <= i && i <= n;
        invariant (bulls as nat) + reccbull(sseq, useq, i) == reccbull(sseq, useq, 0);
        invariant (cows as nat) + recccow(sseq, useq, i) == recccow(sseq, useq, 0);
        invariant nomultiples(sseq) && nomultiples(useq);
        decreases n - i;
    {
        let iu: usize = i as usize;
        let si: u32 = s[iu];
        let ui: u32 = u[iu];

        if si == ui {
            proof {
                assert(0 <= i && i < n);
                assert(sseq@[i] == si as nat);
                assert(useq@[i] == ui as nat);
                assert(reccbull(sseq, useq, i) == reccbull(sseq, useq, i + 1) + 1);
            }
            bulls = bulls + 1;
        } else {
            let mut found: bool = false;
            let mut j: int = 0;
            while j < n
                invariant 0 <= j && j <= n;
                invariant found == (exists |k: int| 0 <= k && k < j && sseq@[k] == useq@[i]);
                decreases n - j;
            {
                let ju: usize = j as usize;
                if !found {
                    if s[ju] == ui {
                        proof {
                            // j is in bounds
                            assert(0 <= j && j < n);
                            assert(sseq@[j] == s[ju] as nat);
                            assert(useq@[i] == ui as nat);
                            // witness j shows existence for j+1
                            assert(0 <= j && j < j + 1);
                            assert(exists |k: int| 0 <= k && k < (j + 1) && sseq@[k] == useq@[i]);
                        }
                        found = true;
                    }
                }
                j = j + 1;
            }

            if found {
                proof {
                    assert(0 <= i && i < n);
                    assert(sseq@[i] == si as nat);
                    assert(useq@[i] == ui as nat);
                    assert(si as nat != ui as nat);
                    // from inner loop invariant at exit j == n we get existence of some k < n with equality
                    assert(exists |k: int| 0 <= k && k < n && sseq@[k] == useq@[i]);
                    assert(recccow(sseq, useq, i) == recccow(sseq, useq, i + 1) + 1);
                }
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