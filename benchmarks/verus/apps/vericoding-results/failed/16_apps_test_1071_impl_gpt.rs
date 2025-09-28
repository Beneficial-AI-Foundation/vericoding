// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: Seq<int>, b: Seq<int>, n: int) -> bool {
    a.len() >= 0 && b.len() >= 0 &&
    (forall|i: int| 0 <= i < a.len() ==> a[i] >= 0) &&
    (forall|j: int| 0 <= j < b.len() ==> b[j] >= 0) &&
    n >= 1
}

spec fn sum_seq(s: Seq<int>) -> int
    recommends forall|i: int| 0 <= i < s.len() ==> s[i] >= 0
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum_seq(s.drop_first()) }
}

spec fn shelves_needed(total: int, capacity: int) -> int
    recommends capacity > 0
{
    if total == 0 { 0 } else { (total - 1) / capacity + 1 }
}

spec fn can_place_all(a: Seq<int>, b: Seq<int>, n: int) -> bool
    recommends valid_input(a, b, n)
{
    let total_cups = sum_seq(a);
    let total_medals = sum_seq(b);
    let shelves_for_cups = shelves_needed(total_cups, 5);
    let shelves_for_medals = shelves_needed(total_medals, 10);
    shelves_for_cups + shelves_for_medals <= n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added decreases for recursive proof showing nonnegativity of sum_seq */
proof fn lemma_sum_seq_nonneg(s: Seq<int>)
    requires
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
    ensures
        sum_seq(s) >= 0,
    decreases s.len()
{
    if s.len() == 0 {
        assert(sum_seq(s) == 0);
    } else {
        lemma_sum_seq_nonneg(s.drop_first());
        assert(sum_seq(s) == s[0] + sum_seq(s.drop_first()));
        assert(s[0] >= 0);
        assert(sum_seq(s.drop_first()) >= 0);
        assert(sum_seq(s) >= 0);
    }
}

/* helper modified by LLM (iteration 5): step lemma for sum of prefix: sum_seq(s.take(k+1)) = sum_seq(s.take(k)) + s[k] */
proof fn lemma_sum_take_step(s: Seq<int>, k: int)
    requires
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
        0 <= k < s.len(),
    ensures
        sum_seq(s.take(k + 1)) == sum_seq(s.take(k)) + s[k],
    decreases k
{
    if k == 0 {
        assert(s.take(1).len() == 1);
        assert(sum_seq(s.take(1)) == s[0] + sum_seq((s.take(1)).drop_first()));
        assert((s.take(1)).drop_first() == s.drop_first().take(0));
        assert(sum_seq(s.drop_first().take(0)) == 0);
        assert(sum_seq(s.take(0)) == 0);
        assert(sum_seq(s.take(1)) == sum_seq(s.take(0)) + s[0]);
    } else {
        let s1 = s.drop_first();
        let k1 = k - 1;
        assert(k1 >= 0);
        assert(s1.len() == s.len() - 1);
        assert(k1 < s1.len());
        lemma_sum_take_step(s1, k1);
        assert(sum_seq(s.take(k + 1)) == s[0] + sum_seq((s.take(k + 1)).drop_first()));
        assert((s.take(k + 1)).drop_first() == s1.take(k));
        assert(sum_seq(s.take(k)) == s[0] + sum_seq((s.take(k)).drop_first()));
        assert((s.take(k)).drop_first() == s1.take(k1));
        assert(s1[k1] == s[k]);
        assert(sum_seq(s1.take(k)) == sum_seq(s1.take(k1)) + s1[k1]);
        assert(sum_seq(s.take(k + 1)) == sum_seq(s.take(k)) + s[k]);
    }
}

/* helper modified by LLM (iteration 5): lemma instantiating shelves_needed definition */
proof fn lemma_shelves_formula(total: int, capacity: int)
    requires
        capacity > 0,
        total >= 0,
    ensures
        shelves_needed(total, capacity) == if total == 0 { 0 } else { (total - 1) / capacity + 1 },
{
    assert(shelves_needed(total, capacity) == if total == 0 { 0 } else { (total - 1) / capacity + 1 });
}

// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>, b: Vec<i8>, n: i8) -> (result: String)
    requires valid_input(a@.map(|i: int, x: i8| x as int), b@.map(|i: int, x: i8| x as int), n as int)
    ensures result@ == (if can_place_all(a@.map(|i: int, x: i8| x as int), b@.map(|i: int, x: i8| x as int), n as int) { "YES"@ } else { "NO"@ })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed proofs to avoid a@.len() parsing and used map index relation */
    let mut i: usize = 0;
    let mut sum_a: int = 0;
    while i < a.len()
        invariant
            0 <= i as int,
            i as int <= a.len() as int,
            sum_a == sum_seq(a@.map(|i: int, x: i8| x as int).take(i as int)),
        decreases a.len() as int - i as int
    {
        proof {
            let sa = a@.map(|i: int, x: i8| x as int);
            assert(sa.len() == a.len() as int);
            assert(i < a.len());
            assert(i as int < sa.len());
            lemma_sum_take_step(sa, i as int);
            assert(sa[i as int] == a[i] as int);
        }
        sum_a = sum_a + a[i] as int;
        i += 1;
    }
    proof {
        let sa = a@.map(|i: int, x: i8| x as int);
        assert(i as int == a.len() as int);
        assert(sum_a == sum_seq(sa.take(i as int)));
        assert(sa.take(i as int) == sa);
    }

    let mut j: usize = 0;
    let mut sum_b: int = 0;
    while j < b.len()
        invariant
            0 <= j as int,
            j as int <= b.len() as int,
            sum_b == sum_seq(b@.map(|i: int, x: i8| x as int).take(j as int)),
        decreases b.len() as int - j as int
    {
        proof {
            let sb = b@.map(|i: int, x: i8| x as int);
            assert(sb.len() == b.len() as int);
            assert(j < b.len());
            assert(j as int < sb.len());
            lemma_sum_take_step(sb, j as int);
            assert(sb[j as int] == b[j] as int);
        }
        sum_b = sum_b + b[j] as int;
        j += 1;
    }
    proof {
        let sb = b@.map(|i: int, x: i8| x as int);
        assert(j as int == b.len() as int);
        assert(sum_b == sum_seq(sb.take(j as int)));
        assert(sb.take(j as int) == sb);
    }

    let shelves_cups: int = if sum_a == 0 { 0 } else { (sum_a - 1) / 5 + 1 };
    let shelves_medals: int = if sum_b == 0 { 0 } else { (sum_b - 1) / 10 + 1 };
    let cond: bool = shelves_cups + shelves_medals <= n as int;

    let res = if cond { "YES".to_string() } else { "NO".to_string() };

    proof {
        let sa = a@.map(|i: int, x: i8| x as int);
        let sb = b@.map(|i: int, x: i8| x as int);
        assert(sum_a == sum_seq(sa));
        assert(sum_b == sum_seq(sb));
        lemma_sum_seq_nonneg(sa);
        lemma_sum_seq_nonneg(sb);
        lemma_shelves_formula(sum_a, 5);
        lemma_shelves_formula(sum_b, 10);
        assert(shelves_needed(sum_a, 5) == shelves_cups);
        assert(shelves_needed(sum_b, 10) == shelves_medals);
        assert(can_place_all(sa, sb, n as int) == (shelves_cups + shelves_medals <= n as int));
        assert((if cond { "YES"@ } else { "NO"@ }) == (if can_place_all(sa, sb, n as int) { "YES"@ } else { "NO"@ }));
    }

    res
}
// </vc-code>


}

fn main() {}