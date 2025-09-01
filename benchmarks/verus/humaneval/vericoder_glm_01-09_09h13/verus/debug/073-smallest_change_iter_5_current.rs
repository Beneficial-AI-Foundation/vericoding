use vstd::prelude::*;

verus! {

spec fn zip_halves<T>(v: Seq<T>) -> (ret: Seq<(T, T)>) {
    v.take((v.len() / 2) as int).zip_with(v.skip(((v.len() + 1) / 2) as int).reverse())
}
// pure-end
// pure-end

spec fn diff(s: Seq<(i32, i32)>) -> (ret: int) {
    s.fold_left(
        0,
        |acc: int, x: (i32, i32)|
            if (x.0 != x.1) {
                acc + 1
            } else {
                acc
            },
    )
}
// pure-end

// <vc-helpers>
spec fn zip_halves_slice<T>(v: Seq<T>, start: int, end: int) -> (ret: Seq<(T, T)>)
    requires 0 <= start <= end <= v.len()
{
    v.take(end as int).skip(start as int).zip_with(
        v.take(v.len() - start as int).skip(v.len() - end as int).reverse()
    )
}

spec fn diff_slice(s: Seq<(i32, i32)>, start: int, end: int) -> (ret: int)
    requires 0 <= start <= end <= s.len()
{
    s.take(end as int).skip(start as int).fold_left(
        0,
        |acc: int, x: (i32, i32)|
            if (x.0 != x.1) {
                acc + 1
            } else {
                acc
            },
    )
}

proof fn diff_take_lemma(s: Seq<(i32, i32)>, n: int)
    requires 0 <= n <= s.len()
    ensures diff(s.take(n)) == diff_slice(s, 0, n)
{
    reveal(diff);
    reveal(diff_slice);
}

spec fn diff_push_back(s: Seq<(i32, i32)>, e: (i32, i32)) -> (ret: int)
    decreases s.len(),
{
    if s.len() == 0 {
        if e.0 != e.1 { 1 } else { 0 }
    } else {
        let last = s.last();
        let init = s.drop_last();
        diff_push_back(init, (last.0, last.1)) + if e.0 != e.1 { 1 } else { 0 }
    }
}

proof fn diff_push_back_lemma(s: Seq<(i32, i32)>, e: (i32, i32))
    ensures diff(s.push_back(e)) == diff(s) + (if e.0 != e.1 then 1 else 0)
    decreases s.len(),
{
    if s.len() == 0 {
        reveal(diff);
        assert(seq![e] == s.push_back(e));
        assert(diff(s.push_back(e)) == if e.0 != e.1 then 1 else 0);
        assert(diff(s) == 0);
    } else {
        let last = s.last();
        let init = s.drop_last();
        assert(s == init.push_back(last));
        reveal(diff);
        assert(diff(s) == diff(init.push_back(last)));
        assert(s.push_back(e) == init.push_back(last).push_back(e));
        assert(diff(s.push_back(e)) == diff(init.push_back(last).push_back(e)));
        diff_push_back_lemma(init.push_back(last), e);
    }
}
// </vc-helpers>

// <vc-spec>
fn smallest_change(v: Vec<i32>) -> (change: usize)
    // pre-conditions-start
    requires
        v@.len() < usize::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        change == diff(zip_halves(v@)),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = v.len();
    let half = n / 2;
    let mut count = 0;
    for i in 0..half
        invariant
            0 <= i <= half,
            if half > 0 {
                i < n && n - 1 - i >= half
            } else {
                true
            },
            count == diff(zip_halves(v@).take(i as int)),
    {
        if v@[i] != v@[n - 1 - i] {
            count += 1;
        }
        proof {
            let s = zip_halves(v@).take(i as int);
            let e = (v@[i], v@[n - 1 - i]);
            let s_plus_e = zip_halves(v@).take((i + 1) as int);
            assert(s_plus_e == s.push_back(e));
            diff_push_back_lemma(s, e);
            assert(diff(s_plus_e) == diff(s) + (if e.0 != e.1 then 1 else 0));
        }
    }
    count
}
// </vc-code>

fn main() {}
}