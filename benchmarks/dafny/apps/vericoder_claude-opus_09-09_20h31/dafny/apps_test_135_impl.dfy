predicate ValidInput(n: int, k: int)
{
    n >= 1 && k >= 1
}

predicate AllRemaindersDistinct(n: int, k: int)
    requires ValidInput(n, k)
{
    forall i :: 1 <= i <= k ==> n % i == (i - 1)
}

predicate HasNonDistinctRemainder(n: int, k: int)
    requires ValidInput(n, k)
{
    exists i :: 1 <= i <= k && n % i != (i - 1)
}

// <vc-helpers>
lemma PartialCheckImpliesRest(n: int, k: int, j: int)
    requires ValidInput(n, k)
    requires 1 <= j <= k
    requires forall i :: 1 <= i < j ==> n % i == (i - 1)
    requires n % j != (j - 1)
    ensures HasNonDistinctRemainder(n, k)
{
    assert n % j != (j - 1) && 1 <= j <= k;
}

lemma AllCheckedImpliesAllDistinct(n: int, k: int)
    requires ValidInput(n, k)
    requires forall i :: 1 <= i <= k ==> n % i == (i - 1)
    ensures AllRemaindersDistinct(n, k)
{
}

lemma NotAllDistinctImpliesHasNonDistinct(n: int, k: int)
    requires ValidInput(n, k)
    requires !AllRemaindersDistinct(n, k)
    ensures HasNonDistinctRemainder(n, k)
{
    assert exists i :: 1 <= i <= k && n % i != (i - 1);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: string)
    requires ValidInput(n, k)
    ensures result == "Yes\n" <==> AllRemaindersDistinct(n, k)
    ensures result == "No\n" <==> HasNonDistinctRemainder(n, k)
// </vc-spec>
// <vc-code>
{
    var i := 1;
    while i <= k
        invariant 1 <= i <= k + 1
        invariant forall j :: 1 <= j < i ==> n % j == (j - 1)
    {
        if n % i != (i - 1) {
            PartialCheckImpliesRest(n, k, i);
            return "No\n";
        }
        i := i + 1;
    }
    
    assert i == k + 1;
    assert forall j :: 1 <= j < k + 1 ==> n % j == (j - 1);
    assert forall j :: 1 <= j <= k ==> n % j == (j - 1);
    AllCheckedImpliesAllDistinct(n, k);
    return "Yes\n";
}
// </vc-code>

