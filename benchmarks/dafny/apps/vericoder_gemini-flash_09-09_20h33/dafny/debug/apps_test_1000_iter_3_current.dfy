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
        }
        Summation(k - 1); // Inductive call
        assert (k * (k + 1)) / 2 == Summation(k - 1) + k by calc {
            Summation(k - 1) + k;
            ((k - 1) * k) / 2 + k;
            (k*k - k + 2*k) / 2;
            (k*k + k) / 2;
            (k * (k + 1)) / 2;
        }
    }
}

lemma SumOfArithmeticSeries(first: int, last: int, count: int)
    requires count >= 0
    requires first <= last || count == 0
    requires last == first + count - 1 || count == 0 // Added || count == 0 for the base case
    ensures (count * (first + last)) / 2 == (if count == 0 then 0 else SumOfArithmeticSeries(first, last-1, count-1) + last)
{
    if count > 0 {
        SumOfArithmeticSeries(first, last-1, count-1); // Inductive call
        assert ((count - 1) * (first + last - 1)) / 2 + last == (count * (first + last)) / 2 by calc {
            ((count - 1) * (first + last - 1)) / 2 + last;
            (count * (first + last - 1) - (first + last - 1) + 2 * last) / 2;
            (count * first + count * last - count - first - last + 1 + 2 * last) / 2;
            (count * first + count * last - count - first + last + 1) / 2;
            (count * (first + last) - count - first + last + 1) / 2;
            (count * (first + last) - (count + first - last - 1)) / 2;
            (count * (first + last) - (count - (last - first + 1))) / 2;
            (count * (first + last) - (count - count)) / 2; // Since last - first + 1 = count
            (count * (first + last)) / 2;
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
        // Prove that the given formula is equivalent to v + sum of arithmetic series from 1 to remaining, then add remaining * 2
        // v + (1 + 2 + ... + remaining) + 2 * remaining
        // v + (remaining * (remaining + 1)) / 2 + 2 * remaining
        // v + (remaining * (remaining + 1) + 4 * remaining) / 2
        // v + (remaining * remaining + remaining + 4 * remaining) / 2
        // v + (remaining * remaining + 5 * remaining) / 2
        // The original formula is v + remaining * (remaining + 3) / 2.
        // Let's analyze the problem. We pay 'v' to get 'v' cities.
        // We have 'req' total cities to visit.
        // 'remaining' = req - v is the number of cities after the first 'v' that require additional cost.
        // For the first 'v' cities, the cost is 'v'.
        // For the (v+1)-th city, the cost is 1. (total cost v+1, 1 more than previous)
        // For the (v+2)-th city, the cost is 2. (total cost v+1+2, 2 more than previous)
        // ...
        // For the (v+k)-th city, the cost is k.
        // So the additional cost is 1 + 2 + ... + (remaining).
        // This sum is (remaining * (remaining + 1)) / 2.
        // However, the problem statement often has a slightly different cost model for 'additional' cities.
        // The problem description implies that for each additional city beyond the initial 'v' cities, the cost increases linearly.
        // If we need 'remaining' additional cities, the costs are 1, 2, ..., remaining.
        // The total cost should be v + Summation(remaining).
        // That is, v + (remaining * (remaining + 1)) / 2.
        // But the provided formula is 'v + remaining * (remaining + 3) / 2'.
        // This implies an additional '2 * remaining' cost:
        // v + (remaining * (remaining + 1)) / 2 + 2 * remaining
        // This means for each 'remaining' city, there's an additional cost of 2.
        // The code implements the formula. We need to verify that this formula holds.
        // The formula for sum of 1...k is Summation(k).
        // The formula remaining * (remaining + 3) / 2 can be written as:
        // (remaining * (remaining + 1) + remaining * 2) / 2
        // = (remaining * (remaining + 1)) / 2 + remaining * 2 / 2
        // = Summation(remaining) + remaining.
        // So the formula is v + Summation(remaining) + remaining.
        // It means the cost for the 'k'-th additional city is 'k+1'. Total sum becomes (1+1)+(2+1)+...+(remaining+1) = (1+2+...+remaining) + remaining*1 = Summation(remaining) + remaining.
        // Ok, so the formula is consistent with the cost model being '1, 2, 3, ... remaining' plus one extra per city, i.e., '2, 3, 4, ... remaining+1'.
        // Sum of arithmetic series from first=2, last=remaining+1, count=remaining.
        // (remaining * (2 + remaining + 1)) / 2 = (remaining * (remaining + 3)) / 2.
        // This matches the provided formula.
        // So, we need to prove that v + SumOfArithmeticSeries(2, remaining + 1, remaining) == v + remaining * (remaining + 3) / 2.
        // Which is just proving SumOfArithmeticSeries(2, remaining + 1, remaining) == remaining * (remaining + 3) / 2.
        // This is exactly what the `SumOfArithmeticSeries` lemma proves.
        SumOfArithmeticSeries(2, remaining + 1, remaining);
        result := v + remaining * (remaining + 3) / 2;
    }
    return result;
}
// </vc-code>

