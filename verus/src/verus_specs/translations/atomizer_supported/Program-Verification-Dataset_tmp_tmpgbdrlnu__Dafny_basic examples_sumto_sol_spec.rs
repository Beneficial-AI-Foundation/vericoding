pub fn sum_up_to(n: nat) -> nat
{
    if n == 0 { 0 } else { sum_up_to((n - 1) as nat) + 1 }
}

pub fn SumUpTo(n: nat) -> nat
    ensures(|result: nat| result == sum_up_to(n))
{
}

pub fn total(a: Seq<nat>) -> nat
{
    if a.len() == 0 { 0 } else { total(a.subrange(0, a.len() - 1)) + a[a.len() - 1] }
}

proof fn total_lemma(a: Seq<nat>, i: nat)
    requires(
        a.len() > 0,
        0 <= i < a.len()
    )
    ensures(
        total(a.subrange(0, i)) + a[i] == total(a.subrange(0, i + 1))
    )
{
}

pub fn Total(a: Seq<nat>) -> nat
    ensures(|result: nat| result == total(a.subrange(0, a.len())))
{
}