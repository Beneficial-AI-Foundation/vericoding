predicate ValidInput(n: int, a: seq<int>)
{
    n >= 1 && |a| == n
}

function CountLocalExtrema(n: int, a: seq<int>): int
    requires ValidInput(n, a)
{
    |set i | 1 <= i < n - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]))|
}

predicate IsLocalExtremum(a: seq<int>, i: int)
    requires 0 <= i < |a|
{
    1 <= i < |a| - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]))
}

// <vc-helpers>
lemma CountLocalExtremaLemma(n: int, a: seq<int>)
    requires ValidInput(n, a)
    ensures CountLocalExtrema(n, a) == |set i | 1 <= i < n - 1 && IsLocalExtremum(a, i)|
{
}

lemma SetCardinalityEqualityLemma(a: seq<int>, i: int, j: int)
    requires 0 <= i <= j <= |a|
    ensures |set k | i <= k < j && IsLocalExtremum(a, k)| == |set k | i <= k < j && ((a[k] > a[k-1] && a[k] > a[k+1]) || (a[k] < a[k-1] && a[k] < a[k+1]))|
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures result >= 0
    ensures n <= 2 ==> result == 0
    ensures n > 2 ==> result <= n - 2
    ensures result == CountLocalExtrema(n, a)
// </vc-spec>
// <vc-code>
{
    result := 0;
    if (n <= 2) {
        return;
    }
    var i := 1;
    while (i < n - 1)
        invariant 1 <= i <= n - 1
        invariant result == |set j | 1 <= j < i && ((a[j] > a[j-1] && a[j] > a[j+1]) || (a[j] < a[j-1] && a[j] < a[j+1]))|
    {
        if ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1])) {
            result := result + 1;
        }
        i := i + 1;
    }
}
// </vc-code>

