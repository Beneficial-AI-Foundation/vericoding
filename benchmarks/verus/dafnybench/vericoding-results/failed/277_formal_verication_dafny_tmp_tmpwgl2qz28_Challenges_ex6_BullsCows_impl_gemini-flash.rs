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
spec fn non_duplicates_in_range(s: Seq<u32>, lo: int, hi: int) -> bool
    decreases hi - lo
{
    if lo >= hi {
        true
    } else {
        (forall|k: int| lo <= k < hi ==> s[k] != s[hi]) && non_duplicates_in_range(s, lo, hi - 1)
    }
}

proof fn lemma_nomultiples_map_from_non_duplicates_in_range(s: Vec<u32>)
    requires
        non_duplicates_in_range(s@, 0, s.len() - 1)
    ensures
        nomultiples(s@.map(|i, x: u32| x as nat))
{
    assert forall|j: int, k: int| 0 <= j < k < s.len() implies s@[j] as nat != s@[k] as nat by {
        assert(s@[j] != s@[k]);
    }
    assert(nomultiples(s@.map(|i, x: u32| x as nat)));
}

// These two helper functions are not present in original file.
// They are needed to pass verification.
spec fn reccbull_range(s: Seq<nat>, u: Seq<nat>, i: int, j: int) -> nat
    decreases j - i
{
    if !(0 <= i <= j <= s.len() == u.len()) {
        arbitrary()
    } else if i == j {
        0
    } else if s[i] == u[i] {
        reccbull_range(s, u, i + 1, j) + 1
    } else {
        reccbull_range(s, u, i + 1, j)
    }
}

spec fn recccow_range(s: Seq<nat>, u: Seq<nat>, i: int, j: int) -> nat
    decreases j - i
{
    if !(0 <= i <= j <= s.len() == u.len()) {
        arbitrary()
    } else if i == j {
        0
    } else if s[i] != u[i] && s.contains(u[i]) {
        recccow_range(s, u, i + 1, j) + 1
    } else {
        recccow_range(s, u, i + 1, j)
    }
}

proof fn lemma_reccbull_sub_range(s: Seq<nat>, u: Seq<nat>, i: int, j: int)
    requires
        0 <= i <= j <= s.len() == u.len(),
    ensures
        reccbull(s, u, i) == reccbull_range(s, u, i, j) + reccbull(s, u, j),
    decreases j - i
{
    if i == j {
        assert(reccbull(s, u, i) == reccbull_range(s, u, i, j) + reccbull(s, u, j));
    } else if i < j {
        if s[i] == u[i] {
            assert(reccbull(s, u, i) == reccbull(s, u, i+1) + 1);
            assert(reccbull_range(s, u, i, j) == reccbull_range(s, u, i+1, j) + 1);
            lemma_reccbull_sub_range(s, u, i + 1, j);
            assert(reccbull(s, u, i+1) == reccbull_range(s, u, i+1, j) + reccbull(s, u, j));
            assert(reccbull(s, u, i) == reccbull_range(s, u, i, j) + reccbull(s, u, j));
        } else {
            assert(reccbull(s, u, i) == reccbull(s, u, i+1));
            assert(reccbull_range(s, u, i, j) == reccbull_range(s, u, i+1, j));
            lemma_reccbull_sub_range(s, u, i + 1, j);
            assert(reccbull(s, u, i+1) == reccbull_range(s, u, i+1, j) + reccbull(s, u, j));
            assert(reccbull(s, u, i) == reccbull_range(s, u, i, j) + reccbull(s, u, j));
        }
    }
}

proof fn lemma_recccow_sub_range(s: Seq<nat>, u: Seq<nat>, i: int, j: int)
    requires
        0 <= i <= j <= s.len() == u.len(),
    ensures
        recccow(s, u, i) == recccow_range(s, u, i, j) + recccow(s, u, j),
    decreases j - i
{
    if i == j {
        assert(recccow(s, u, i) == recccow_range(s, u, i, j) + recccow(s, u, j));
    } else if i < j {
        if s[i] != u[i] && s.contains(u[i]) {
            assert(recccow(s, u, i) == recccow(s, u, i+1) + 1);
            assert(recccow_range(s, u, i, j) == recccow_range(s, u, i+1, j) + 1);
            lemma_recccow_sub_range(s, u, i + 1, j);
            assert(recccow(s, u, i+1) == recccow_range(s, u, i+1, j) + recccow(s, u, j));
            assert(recccow(s, u, i) == recccow_range(s, u, i, j) + recccow(s, u, j));
        } else {
            assert(recccow(s, u, i) == recccow(s, u, i+1));
            assert(recccow_range(s, u, i, j) == recccow_range(s, u, i+1, j));
            lemma_recccow_sub_range(s, u, i + 1, j);
            assert(recccow(s, u, i+1) == recccow_range(s, u, i+1, j) + recccow(s, u, j));
            assert(recccow(s, u, i) == recccow_range(s, u, i, j) + recccow(s, u, j));
        }
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
    let n = s.len();

    let ghost s_nat = s@.map(|i, x: u32| x as nat);
    let ghost u_nat = u@.map(|i, x: u32| x as nat);

    let mut i: usize = 0; // Changed type to usize
    while i < n
        invariant
            0 <= i as int <= n as int,
            bulls as nat == reccbull_range(s_nat, u_nat, 0, i as int),
            cows as nat == recccow_range(s_nat, u_nat, 0, i as int),
            s_nat.len() == n as int,
            u_nat.len() == n as int,
            nomultiples(s_nat),
            nomultiples(u_nat),
            s_nat == s@.map(|idx, x: u32| x as nat),
            u_nat == u@.map(|idx, x: u32| x as nat),
    {
        if s[i] == u[i] {
            bulls = bulls + 1;
        } else {
            if s.contains(&u[i]) {
                cows = cows + 1;
            }
        }
        i = i + 1;
    }

    proof {
        lemma_reccbull_sub_range(s_nat, u_nat, 0, n as int);
        lemma_recccow_sub_range(s_nat, u_nat, 0, n as int);
    }
    (bulls, cows)
}
// </vc-code>

fn main() {}

}