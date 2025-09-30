// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(m: int, d: int) -> bool {
    1 <= m <= 12 && 1 <= d <= 7
}

spec fn days_in_month(m: int) -> int {
    if 1 <= m <= 12 {
        seq![31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31][m-1]
    } else {
        0
    }
}

spec fn columns_needed(m: int, d: int) -> int {
    if valid_input(m, d) {
        1 + (d - 1 + days_in_month(m) - 1) / 7
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
fn days_in_month_exec(m: i8) -> (res: i8)
    requires
        1 <= m as int,
        m as int <= 12,
    ensures
        res as int == days_in_month(m as int),
        28 <= res as int,
        res as int <= 31,
{
    let r: i8;
    if m == 2 {
        r = 28;
    } else if m == 4 || m == 6 || m == 9 || m == 11 {
        r = 30;
    } else {
        r = 31;
    }
    proof {
        if m == 2 {
            assert(days_in_month(m as int) == 28);
        } else if m == 4 || m == 6 || m == 9 || m == 11 {
            if m == 4 {
                assert(days_in_month(m as int) == 30);
            } else if m == 6 {
                assert(days_in_month(m as int) == 30);
            } else if m == 9 {
                assert(days_in_month(m as int) == 30);
            } else {
                assert(m == 11);
                assert(days_in_month(m as int) == 30);
            }
        } else {
            if m == 1 { assert(days_in_month(m as int) == 31); }
            else if m == 3 { assert(days_in_month(m as int) == 31); }
            else if m == 5 { assert(days_in_month(m as int) == 31); }
            else if m == 7 { assert(days_in_month(m as int) == 31); }
            else if m == 8 { assert(days_in_month(m as int) == 31); }
            else if m == 10 { assert(days_in_month(m as int) == 31); }
            else { assert(m == 12); assert(days_in_month(m as int) == 31); }
        }
    }
    r
}

proof fn lemma_division_by_7_unique(n: int, k: int, r: int)
    requires
        0 <= n,
        0 <= k,
        r == n - 7 * k,
        0 <= r,
        r < 7,
    ensures
        n / 7 == k,
{
}

// </vc-helpers>

// <vc-spec>
fn solve(m: i8, d: i8) -> (result: i8)
    requires valid_input(m as int, d as int)
    ensures result as int == columns_needed(m as int, d as int) && 4 <= result as int <= 6
// </vc-spec>
// <vc-code>
{
    let dim: i8 = days_in_month_exec(m);

    // Bounds needed to avoid overflow and for reasoning
    assert(1 <= d as int && d as int <= 7);
    assert(28 <= dim as int && dim as int <= 31);

    // Compute n = (d - 1) + (dim - 1)
    let n: i8 = d - 1 + dim - 1;

    let ghost ni: int = d as int + dim as int - 2;
    assert(n as int == ni);
    assert(0 <= ni);

    // Tight bounds on ni
    assert(27 <= ni) by {
        // (d as int - 1) >= 0 and (dim as int - 1) >= 27
        assert(d as int - 1 >= 0);
        assert(dim as int - 1 >= 27);
    }
    assert(ni <= 36) by {
        // (d as int - 1) <= 6 and (dim as int - 1) <= 30
        assert(d as int - 1 <= 6);
        assert(dim as int - 1 <= 30);
    }

    let res: i8;
    if n <= 27 {
        // Then ni == 27
        assert(ni == 27) by {
            assert(n as int == ni);
            assert(ni <= 27);
            assert(27 <= ni);
        }
        res = 4; // 1 + 3
        proof {
            assert(0 <= ni - 7 * 3 && ni - 7 * 3 < 7) by {
                assert(ni - 21 == 6);
            }
            lemma_division_by_7_unique(ni, 3, ni - 7 * 3);
            assert(res as int == 1 + ni / 7);
        }
    } else if n <= 34 {
        // 28 <= ni <= 34
        assert(28 <= ni && ni <= 34) by {
            assert(n as int == ni);
            assert(27 < ni);
            assert(ni <= 34);
        }
        res = 5; // 1 + 4
        proof {
            assert(0 <= ni - 7 * 4 && ni - 7 * 4 < 7) by {
                assert(ni - 28 >= 0);
                assert(ni - 28 <= 6);
            }
            lemma_division_by_7_unique(ni, 4, ni - 7 * 4);
            assert(res as int == 1 + ni / 7);
        }
    } else {
        // 35 <= ni <= 36
        assert(35 <= ni && ni <= 36) by {
            assert(n as int == ni);
            assert(ni >= 35);
            assert(ni <= 36);
        }
        res = 6; // 1 + 5
        proof {
            assert(0 <= ni - 7 * 5 && ni - 7 * 5 < 7) by {
                assert(ni - 35 >= 0);
                assert(ni - 35 <= 1);
            }
            lemma_division_by_7_unique(ni, 5, ni - 7 * 5);
            assert(res as int == 1 + ni / 7);
        }
    }

    // Connect to columns_needed spec
    assert(valid_input(m as int, d as int));
    assert(columns_needed(m as int, d as int) == 1 + ((d as int - 1) + (days_in_month(m as int) - 1)) / 7);
    assert(days_in_month(m as int) == dim as int);
    assert(columns_needed(m as int, d as int) == 1 + (ni / 7));

    assert(4 <= res as int && res as int <= 6);
    res
}
// </vc-code>


}

fn main() {}