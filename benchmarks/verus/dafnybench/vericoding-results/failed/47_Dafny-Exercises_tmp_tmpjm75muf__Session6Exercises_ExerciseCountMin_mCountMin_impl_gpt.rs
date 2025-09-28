use vstd::prelude::*;

verus! {

spec fn min(v: Seq<int>, i: int) -> int
    decreases i
{
    if 1 <= i <= v.len() {
        if i == 1 {
            v[0]
        } else if v[i-1] <= min(v, i-1) {
            v[i-1]
        } else {
            min(v, i-1)
        }
    } else {
        0  // dummy value for invalid inputs
    }
}

proof fn min_property(v: Seq<int>, i: int)
    requires 1 <= i <= v.len()
    ensures forall|k: int| 0 <= k < i ==> v[k] >= min(v, i)
    decreases i
{
    if i > 1 {
        min_property(v, i-1);
    }
}

spec fn count_min(v: Seq<int>, x: int, i: int) -> int
    decreases i
{
    if 0 <= i <= v.len() {
        if i == 0 {
            0
        } else if v[i-1] == x {
            1 + count_min(v, x, i-1)
        } else {
            count_min(v, x, i-1)
        }
    } else {
        0  // dummy value for invalid inputs
    }
}

proof fn count_min_property(v: Seq<int>, x: int, i: int)
    requires 0 <= i <= v.len()
    ensures !(exists|k: int| 0 <= k < i && v[k] == x) ==> count_min(v, x, i) == 0
    decreases i
{
    if i > 0 {
        count_min_property(v, x, i-1);
    }
}

// <vc-helpers>
proof fn min_unfold_step(v: Seq<int>, i: int)
    requires 1 < i <= v.len()
    ensures min(v, i) == (if v[i - 1] <= min(v, i - 1) { v[i - 1] } else { min(v, i - 1) })
    decreases i
{
    assert(1 <= i <= v.len());
    assert(i != 1);
    assert(
        min(v, i)
        ==
        (if 1 <= i <= v.len() {
            if i == 1 {
                v[0]
            } else if v[i - 1] <= min(v, i - 1) {
                v[i - 1]
            } else {
                min(v, i - 1)
            }
        } else {
            0
        })
    );
    if v[i - 1] <= min(v, i - 1) {
        assert(min(v, i) == v[i - 1]);
        assert(min(v, i) == (if v[i - 1] <= min(v, i - 1) { v[i - 1] } else { min(v, i - 1) }));
    } else {
        assert(min(v, i) == min(v, i - 1));
        assert(min(v, i) == (if v[i - 1] <= min(v, i - 1) { v[i - 1] } else { min(v, i - 1) }));
    }
}

proof fn min_base(v: Seq<int>)
    requires 1 <= v.len()
    ensures min(v, 1) == v[0]
{
    assert(1 <= 1 <= v.len());
    assert(
        min(v, 1)
        ==
        (if 1 <= 1 <= v.len() {
            if 1 == 1 {
                v[0]
            } else if v[1 - 1] <= min(v, 1 - 1) {
                v[1 - 1]
            } else {
                min(v, 1 - 1)
            }
        } else {
            0
        })
    );
    assert(min(v, 1) == v[0]);
}

proof fn count_min_unfold_step(v: Seq<int>, x: int, i: int)
    requires 0 < i <= v.len()
    ensures count_min(v, x, i) ==
        (if v[i - 1] == x { 1 + count_min(v, x, i - 1) } else { count_min(v, x, i - 1) })
    decreases i
{
    assert(0 <= i <= v.len());
    assert(i != 0);
    assert(
        count_min(v, x, i)
        ==
        (if 0 <= i <= v.len() {
            if i == 0 {
                0
            } else if v[i - 1] == x {
                1 + count_min(v, x, i - 1)
            } else {
                count_min(v, x, i - 1)
            }
        } else {
            0
        })
    );
    if v[i - 1] == x {
        assert(count_min(v, x, i) == 1 + count_min(v, x, i - 1));
        assert(count_min(v, x, i) ==
            (if v[i - 1] == x { 1 + count_min(v, x, i - 1) } else { count_min(v, x, i - 1) }));
    } else {
        assert(count_min(v, x, i) == count_min(v, x, i - 1));
        assert(count_min(v, x, i) ==
            (if v[i - 1] == x { 1 + count_min(v, x, i - 1) } else { count_min(v, x, i - 1) }));
    }
}
// </vc-helpers>

// <vc-spec>
fn m_count_min(v: &Vec<i32>) -> (c: i32)
    requires v.len() > 0
    ensures c == count_min(v@.map_values(|x: i32| x as int), 
                          min(v@.map_values(|x: i32| x as int), v.len() as int), 
                          v.len() as int)
    //Implement and verify an O(v.len()) algorithm
// </vc-spec>
// <vc-code>
{
    let n = v.len();
    let ghost s = v@.map_values(|x: i32| x as int);

    proof {
        assert(s.len() == n as int);
        assert(n > 0);
        assert(1 <= n as int);
        min_base(s);
        assert(min(s, 1) == s[0]);
        assert(s[0] == v@[0] as int);
    }

    let mut i: usize = 1;
    let mut m: i32 = v[0];

    while i < n
        invariant
            1 <= i as int <= n as int,
            s.len() == n as int,
            m as int == min(s, i as int),
            n > 0
    {
        let x = v[i];
        let new_m = if x <= m { x } else { m };

        proof {
            let ii = i as int;
            assert(0 <= ii < s.len());
            assert(s[ii] == v@[ii] as int);
            assert(v@[ii] == x);
            let k = ii + 1;
            assert(1 < k <= s.len());
            min_unfold_step(s, k);
            if x <= m {
                assert((x as int) <= (m as int));
                assert(s[ii] <= min(s, ii));
                assert(min(s, k) == s[ii]);
                assert(new_m == x);
                assert(new_m as int == s[ii]);
                assert(new_m as int == min(s, k));
            } else {
                assert(x > m);
                assert((x as int) > (m as int));
                assert(s[ii] > min(s, ii));
                assert(min(s, k) == min(s, ii));
                assert(new_m == m);
                assert(new_m as int == min(s, k));
            }
        }

        m = new_m;
        i = i + 1;
    }

    proof {
        assert(i == n);
        assert(m as int == min(s, n as int));
    }

    let mm = m;

    let mut cnt: i32 = 0;
    let mut j: usize = 0;

    while j < n
        invariant
            j as int <= n as int,
            s.len() == n as int,
            mm as int == min(s, n as int),
            cnt as int == count_min(s, mm as int, j as int)
    {
        let x = v[j];
        if x == mm {
            cnt = cnt + 1;
        }

        proof {
            let jj = j as int;
            assert(0 <= jj < s.len());
            assert(s[jj] == v@[jj] as int);
            assert(v@[jj] == x);
            let k = jj + 1;
            assert(0 < k <= s.len());
            count_min_unfold_step(s, mm as int, k);
            if x == mm {
                assert(s[jj] == mm as int);
                assert(count_min(s, mm as int, k) == 1 + count_min(s, mm as int, jj));
                assert(cnt as int == count_min(s, mm as int, k));
            } else {
                assert(s[jj] != mm as int);
                assert(count_min(s, mm as int, k
// </vc-code>

fn main() {
}

}