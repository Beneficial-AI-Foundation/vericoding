// <vc-preamble>
predicate ValidInput(n: int, L: int, costs: seq<int>)
{
    1 <= n <= 30 && 1 <= L <= 1000000000 &&
    |costs| == n &&
    forall i :: 0 <= i < n ==> 1 <= costs[i] <= 1000000000
}

function power2(k: int): int
    requires k >= 0
    ensures power2(k) >= 1
    ensures k > 0 ==> power2(k) == 2 * power2(k - 1)
{
    if k == 0 then 1 else 2 * power2(k - 1)
}

function min(a: int, b: int): int
    ensures min(a, b) == a || min(a, b) == b
    ensures min(a, b) <= a && min(a, b) <= b
{
    if a <= b then a else b
}
// </vc-preamble>

// <vc-helpers>
method findK(l: int) returns (k: int)
    requires l >= 1
    requires l <= 1000000000
    ensures k >= 0
    ensures k <= 34
    ensures power2(k) >= l
    ensures k == 0 || power2(k - 1) < l
{
    k := 0;
    while power2(k) < l && k < 34
        invariant k >= 0
        invariant k <= 34
        invariant power2(k) >= 1
        invariant forall j :: 0 <= j < k ==> power2(j) < l
    {
        k := k + 1;
    }
    if power2(k) < l {
        k := 34;
        assert power2(30) >= 1073741824;
        assert power2(34) >= power2(30);
        assert power2(34) >= 1073741824;
        assert l <= 1000000000;
        assert power2(34) >= l;
    }
}

method solveRec(a: seq<int>, l: int) returns (result: int)
    requires |a| >= 35
    requires l >= 0
    requires l <= 1000000000
    requires forall i :: 0 <= i < |a| ==> a[i] >= 1
    ensures l == 0 ==> result == 0
    ensures l == 1 ==> result == a[0]
    ensures l >= 2 ==> result >= 0
    ensures result >= 0
{
    if l == 0 {
        result := 0;
    } else if l == 1 {
        result := a[0];
    } else {
        var k := findK(l);
        var power2k_minus_1 := power2(k - 1);
        var rec_result := solveRec(a, l - power2k_minus_1);
        assert k >= 1;
        assert k <= 34;
        assert k < |a|;
        var tmpCall1 := min(a[k], a[k - 1] + rec_result);
        result := tmpCall1;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, L: int, costs: seq<int>) returns (result: int)
    requires ValidInput(n, L, costs)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    // Preprocess the costs array
    var a := costs;

    // Right to left pass
    if n >= 2 {
        var i := n - 2;
        while i >= 0
            invariant -1 <= i <= n - 2
            invariant |a| == n
            invariant forall j :: 0 <= j < n ==> a[j] >= 1
            invariant forall j :: i + 2 <= j < n ==> a[j - 1] <= a[j]
        {
            if a[i] > a[i + 1] {
                a := a[i := a[i + 1]];
            }
            i := i - 1;
        }
    }

    // Left to right pass  
    if n >= 2 {
        var i := 1;
        while i < n
            invariant 1 <= i <= n
            invariant |a| == n
            invariant forall j :: 0 <= j < n ==> a[j] >= 1
            invariant forall j :: 1 <= j < i ==> a[j] <= 2 * a[j - 1]
        {
            if a[i] > 2 * a[i - 1] {
                a := a[i := 2 * a[i - 1]];
            }
            i := i + 1;
        }
    }

    // Extend array to length 35
    while |a| < 35
        invariant |a| >= n
        invariant forall j :: 0 <= j < |a| ==> a[j] >= 1
    {
        a := a + [2 * a[|a| - 1]];
    }

    result := solveRec(a, L);
}
// </vc-code>
