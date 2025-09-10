predicate ValidInput(n: int, v: int) {
    2 <= n <= 100 && 1 <= v <= 100
}

function MinCost(n: int, v: int): int
    requires ValidInput(n, v)
{
    var req := n - 1;
    if req <= v then
        req
    else
        var remaining := req - v;
        v + remaining * (remaining + 3) / 2
}

// <vc-helpers>
lemma Summation(k: int)
    requires k >= 0
    ensures (k * (k + 1)) / 2 == (if k == 0 then 0 else Summation(k - 1) + k)
{
    if k > 0 {
        calc {
            (k * (k + 1)) / 2;
            (k * k + k) / 2;
            ((k - 1 + 1) * (k - 1 + 2)) / 2;
        }
        assert (k * (k + 1)) / 2 == Summation(k - 1) + k by (calc {
            Summation(k - 1) + k;
            ((k - 1) * k) / 2 + k;
            (k*k - k + 2*k) / 2;
            (k*k + k) / 2;
            (k * (k + 1)) / 2;
        });
    }
}

lemma SumOfArithmeticSeries(first: int, last: int, count: int)
    requires count >= 0
    requires first <= last
    requires last == first + count - 1 // if count = 0, last = first -1
    ensures (count * (first + last)) / 2 == (if count == 0 then 0 else SumOfArithmeticSeries(first, last-1, count-1) + last)
{
    if count > 0 {
        assert SumOfArithmeticSeries(first, last-1, count-1) + last == ((count - 1) * (first + last - 1)) / 2 + last by {
            SumOfArithmeticSeries(first, last - 1, count - 1);
        }
        assert (((count - 1) * (first + last - 1)) / 2) + last == (count * (first + last)) / 2 by {
            calc {
                ((count - 1) * (first + last - 1)) / 2 + last;
                (count * (first + last - 1) - (first + last - 1) + 2 * last) / 2;
                (count * (first + last) - count - first - last + 1 + 2 * last) / 2; // (count * first + count * last - count) - (first + last - 1) + (2 * last)
                (count * first + count * last - count - first + last + 1) / 2; // (count * (first + last) - count - first - last + 1 + 2 * last) / 2; //
            }
            assert (count * (first + last) - count * 1 - first + last + 1) == (count * (first + last) - count - first + last + 1);
            assert (count * (first + last) - count * 1 - first + last + 1) == (count * (first + last) - count - (first - last - 1));
            assert (count * first + count * last - count * 1 - first + last + 1) == (count * first + count * last - (count + first - last - 1));
            assert (count * (first + last) - count - first + last + 1) == (count * first + count * last - count - first + last + 1);
            assert (count * first + count * last - count + first + 1) == (count * first + count * last - count + first + 1);
            assert (count * first + count * last - count - first + last + 1) == (count * first + count * last + (-count - first + last + 1));
            // This entire lemma is not necessary for the verification itself, only for reasoning about the result.
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, v: int) returns (result: int)
    requires ValidInput(n, v)
    ensures result == MinCost(n, v)
// </vc-spec>
// <vc-code>
{
    var req := n - 1;
    if req <= v {
        result := req;
    } else {
        var remaining := req - v;
        result := v + remaining * (remaining + 3) / 2;
    }
    return result;
}
// </vc-code>

