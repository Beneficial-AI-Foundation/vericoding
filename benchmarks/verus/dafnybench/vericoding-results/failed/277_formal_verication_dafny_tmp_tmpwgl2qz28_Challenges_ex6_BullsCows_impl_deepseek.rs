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
spec fn count_elems_up_to(seq: Seq<nat>, x: nat, end: int) -> nat
    decreases end
{
    if end <= 0 {
        0
    } else {
        let count_prev = count_elems_up_to(seq, x, end - 1);
        if end - 1 < seq.len() && seq[end - 1] == x {
            count_prev + 1
        } else {
            count_prev
        }
    }
}

proof fn count_elems_up_to_lemma(seq: Seq<nat>, x: nat, i: int)
    requires
        0 <= i <= seq.len()
    ensures
        count_elems_up_to(seq, x, i) == seq.subrange(0, i).filter(|y: nat| y == x).len()
{
    reveal_with_fuel(Seq::filter, 2);
    if i > 0 {
        count_elems_up_to_lemma(seq, x, i - 1);
    }
}

spec fn common_count(s: Seq<nat>, u: Seq<nat>) -> nat {
    let mut total: nat = 0;
    let mut k: nat = 0;
    while k < 10
        invariant
            0 <= k <= 10,
            total == common_count_range(s, u, k)
        decreases 10 - k
    {
        let s_count = s.filter(|x: nat| *x == k).len();
        let u_count = u.filter(|x: nat| *x == k).len();
        total = total + (if s_count < u_count { s_count } else { u_count });
        k = k + 1;
    }
    total
}

spec fn common_count_range(s: Seq<nat>, u: Seq<nat>, up_to: nat) -> nat {
    let mut total: nat = 0;
    let mut k: nat = 0;
    while k < up_to
        invariant
            0 <= k <= up_to,
            total == common_count_range_loop(s, u, k)
        decreases up_to - k
    {
        let s_count = s.filter(|x: nat| *x == k).len();
        let u_count = u.filter(|x: nat| *x == k).len();
        total = total + (if s_count < u_count { s_count } else { u_count });
        k = k + 1;
    }
    total
}

spec fn common_count_range_loop(s: Seq<nat>, u: Seq<nat>, up_to: nat) -> nat {
    if up_to == 0 {
        0
    } else {
        let s_count = s.filter(|x: nat| *x == up_to - 1).len();
        let u_count = u.filter(|x: nat| *x == up_to - 1).len();
        common_count_range_loop(s, u, up_to - 1) + (if s_count < u_count { s_count } else { u_count })
    }
}

proof fn bulls_cows_relation(s: Seq<nat>, u: Seq<nat>)
    requires
        s.len() == u.len(),
        nomultiples(s) && nomultiples(u)
    ensures
        bullspec(s, u) + cowspec(s, u) <= common_count(s, u),
        bullspec(s, u) == reccbull(s, u, 0)
{
    reveal(reccbull);
    reveal(recccow);
}

proof fn bullspec_equals_count_matches(s: Seq<nat>, u: Seq<nat>, i: int)
    requires
        0 <= i <= s.len() == u.len()
    ensures
        reccbull(s, u, i) == count_matches(s, u, i)
{
    reveal(reccbull);
}

spec fn count_matches(s: Seq<nat>, u: Seq<nat>, start: int) -> nat {
    if start >= s.len() {
        0
    } else {
        (if s[start] == u[start] { 1nat } else { 0nat }) + count_matches(s, u, start + 1)
    }
}

proof fn cowspec_equals_common_excluding_bulls(s: Seq<nat>, u: Seq<nat>)
    requires
        s.len() == u.len(),
        nomultiples(s) && nomultiples(u)
    ensures
        cowspec(s, u) == common_count(s, u) - bullspec(s, u)
{
    reveal(common_count);
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
    let mut bulls = 0;
    let mut cows = 0;
    let n = s.len();
    
    let mut s_counts: Vec<u32> = Vec::new();
    let mut u_counts: Vec<u32> = Vec::new();
    s_counts.resize(10, 0);
    u_counts.resize(10, 0);
    
    proof {
        bullspec_equals_count_matches(s@.map(|i, x: u32| x as nat), u@.map(|i, x: u32| x as nat), 0);
    }
    
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            bulls as nat == count_matches(s@.map(|i, x: u32| x as nat), u@.map(|i, x: u32| x as nat), i as int),
            forall|k: int| 0 <= k < 10 ==> s_counts@[k] as nat == count_elems_up_to(s@.map(|i, x: u32| x as nat), k as nat, i as int),
            forall|k: int| 0 <= k < 10 ==> u_counts@[k] as nat == count_elems_up_to(u@.map(|i, x: u32| x as nat), k as nat, i as int)
        decreases n - i
    {
        let s_val = s[i] as usize;
        let u_val = u[i] as usize;
        
        if s_val == u_val {
            bulls = bulls + 1;
        }
        
        if s_val < 10 {
            s_counts[s_val] = s_counts[s_val] + 1;
        }
        if u_val < 10 {
            u_counts[u_val] = u_counts[u_val] + 1;
        }
        
        proof {
            count_elems_up_to_lemma(s@.map(|i, x: u32| x as nat), s_val as nat, i as int + 1);
            count_elems_up_to_lemma(u@.map(|i, x: u32| x as nat), u_val as nat, i as int + 1);
        }
        
        i = i + 1;
    }
    
    proof {
        bulls_cows_relation(s@.map(|i, x: u32| x as nat), u@.map(|i, x: u32| x as nat));
        cowspec_equals_common_excluding_bulls(s@.map(|i, x: u32| x as nat), u@.map(|i, x: u32| x as nat));
    }
    
    let mut total_common = 0;
    let mut j = 0;
    while j < 10
        invariant
            0 <= j <= 10,
            total_common as nat == common_count_range(s@.map(|i, x: u32| x as nat), u@.map(|i, x: u32| x as nat), j as nat)
        decreases 10 - j
    {
        total_common = total_common + (if s_counts[j] < u_counts[j] { s_counts[j] } else { u_counts[j] });
        j = j + 1;
    }
    
    cows = total_common - bulls;
    
    (bulls, cows)
}
// </vc-code>

fn main() {}

}