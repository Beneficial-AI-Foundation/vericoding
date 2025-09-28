use vstd::prelude::*;

verus! {

spec fn has_count(v: int, a: Seq<int>, n: nat) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        if a[n-1] == v {
            has_count(v, a, (n-1) as nat) + 1
        } else {
            has_count(v, a, (n-1) as nat)
        }
    }
}

// <vc-helpers>
proof fn lemma_has_count_base(v: int, a: Seq<int>) {
    assert(has_count(v, a, 0) == 0);
}

broadcast proof fn lemma_has_count_step(v: int, a: Seq<int>, n: nat)
    requires n > 0 && n <= a.len()
{
    assert(has_count(v, a, n) == if a[n-1] == v { has_count(v, a, (n-1) as nat) + 1 } else { has_count(v, a, (n-1) as nat) });
}
// </vc-helpers>

// <vc-spec>
fn count(v: i32, a: &[i32], n: usize) -> (r: i32)
    requires n <= a.len()
    ensures n <= a.len() ==> has_count(v as int, a@.map_values(|x: i32| x as int), n as nat) == r as int
// </vc-spec>
// <vc-code>
{
    proof {
        let s: Seq<int> = a@.map_values(|x: i32| x as int);
        lemma_has_count_base(v as int, s);
    }
    let mut cnt: i32 = 0;
    let mut i: usize = 0;
    while i < n
        invariant n <= a.len()
        invariant i <= n
        invariant i <= a.len()
        invariant cnt == has_count(v as int, a@.map_values(|x: i32| x as int), i as nat)
    {
        proof {
            let s: Seq<int> = a@.map_values(|x: i32| x as int);
            lemma_has_count_step(v as int, s, (i+1) as nat);
        }
        if a[i] == v {
            cnt = cnt + 1;
        }
        i = i + 1;
    }
    cnt
}
// </vc-code>

fn main() {
}

}