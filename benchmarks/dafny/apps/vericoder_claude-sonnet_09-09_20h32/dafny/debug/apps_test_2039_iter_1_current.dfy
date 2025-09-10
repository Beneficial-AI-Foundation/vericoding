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
lemma LocalExtremumEquivalence(a: seq<int>, i: int)
    requires 0 <= i < |a|
    ensures IsLocalExtremum(a, i) <==> (1 <= i < |a| - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1])))
{
}

lemma CountInvariant(a: seq<int>, i: int, count: int, extremaSet: set<int>)
    requires ValidInput(|a|, a)
    requires 1 <= i <= |a| - 1
    requires extremaSet == set j | 1 <= j < i && IsLocalExtremum(a, j)
    requires count == |extremaSet|
    ensures count <= i - 1
{
}

lemma FinalCountCorrectness(a: seq<int>, count: int, extremaSet: set<int>)
    requires ValidInput(|a|, a)
    requires extremaSet == set j | 1 <= j < |a| - 1 && IsLocalExtremum(a, j)
    requires count == |extremaSet|
    ensures count == CountLocalExtrema(|a|, a)
{
    var defSet := set i | 1 <= i < |a| - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]));
    assert extremaSet == defSet by {
        forall j | j in extremaSet ensures j in defSet {
            LocalExtremumEquivalence(a, j);
        }
        forall j | j in defSet ensures j in extremaSet {
            LocalExtremumEquivalence(a, j);
        }
    }
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
    if n <= 2 {
        return 0;
    }
    
    var count := 0;
    var i := 1;
    
    while i < n - 1
        invariant 1 <= i <= n - 1
        invariant count == |set j | 1 <= j < i && IsLocalExtremum(a, j)|
        invariant count <= i - 1
    {
        if IsLocalExtremum(a, i) {
            count := count + 1;
        }
        i := i + 1;
    }
    
    FinalCountCorrectness(a, count, set j | 1 <= j < n - 1 && IsLocalExtremum(a, j));
    return count;
}
// </vc-code>

