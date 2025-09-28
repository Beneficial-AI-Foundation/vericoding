// <vc-preamble>
use vstd::prelude::*;

verus! {

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
// </vc-preamble>

// <vc-helpers>
fn vec_contains(v: &Vec<u32>, val: u32) -> (b: bool)
    ensures
        b == v@.map(|i, x: u32| x as nat).contains(val as nat),
{
    let mut j: usize = 0;
    while j < v.len()
        invariant
            j <= v.len(),
            forall|k: int| 0 <= k < j ==> v@[k] != val,
        decreases v.len() - j
    {
        if v[j] == val {
            return true;
        }
        j = j + 1;
    }
    return false;
}

/* helper modified by LLM (iteration 5): added type suffixes to literals to fix compilation errors */
proof fn lemma_reccbull_unfold(s: Seq<nat>, u: Seq<nat>, i: int)
    requires
        0 <= i < s.len() == u.len(),
    ensures
        reccbull(s, u, i) == (if s[i] == u[i] { 1nat } else { 0nat }) + reccbull(s, u, i + 1),
{
}

/* helper modified by LLM (iteration 5): added type suffixes to literals to fix compilation errors */
proof fn lemma_recccow_unfold(s: Seq<nat>, u: Seq<nat>, i: int)
    requires
        0 <= i < s.len() == u.len(),
    ensures
        recccow(s, u, i) == (if s[i] != u[i] && s.contains(u[i]) { 1nat } else { 0nat }) + recccow(s, u, i + 1),
{
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
    /* code modified by LLM (iteration 5): no functional changes needed; the fix was in the helper lemmas */
    let mut bulls: u32 = 0;
    let mut cows: u32 = 0;
    let mut i: usize = 0;
    let len = s.len();

    let ghost s_spec = s@.map(|i, x: u32| x as nat);
    let ghost u_spec = u@.map(|i, x: u32| x as nat);

    while i < len
        invariant
            0 <= i <= len,
            nomultiples(s_spec),
            nomultiples(u_spec),
            bulls as nat == reccbull(s_spec, u_spec, 0) - reccbull(s_spec, u_spec, i as int),
            cows as nat == recccow(s_spec, u_spec, 0) - recccow(s_spec, u_spec, i as int),
        decreases len - i
    {
        proof {
            lemma_reccbull_unfold(s_spec, u_spec, i as int);
            lemma_recccow_unfold(s_spec, u_spec, i as int);
        }
        
        if s[i] == u[i] {
            bulls = bulls + 1;
        } else {
            if vec_contains(&s, u[i]) {
                cows = cows + 1;
            }
        }
        i = i + 1;
    }

    proof {
        assert(reccbull(s_spec, u_spec, len as int) == 0);
        assert(recccow(s_spec, u_spec, len as int) == 0);
    }
    
    (bulls, cows)
}
// </vc-code>

}
fn main() {}