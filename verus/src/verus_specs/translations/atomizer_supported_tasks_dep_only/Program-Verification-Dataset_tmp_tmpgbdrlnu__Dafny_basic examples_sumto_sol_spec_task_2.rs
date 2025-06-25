spec fn total(a: Seq<nat>) -> nat {
    if a.len() == 0 {
        0
    } else {
        total(a.subrange(0, a.len() - 1)) + a[a.len() - 1]
    }
}

proof fn total_lemma(a: Seq<nat>, i: nat)
    requires
        a.len() > 0,
        0 <= i < a.len(),
    ensures
        total(a.subrange(0, i)) + a[i] == total(a.subrange(0, i + 1)),
{
}

pub fn Total(a: Seq<nat>) -> (r: nat)
    ensures
        r == total(a.subrange(0, a.len())),
{
}