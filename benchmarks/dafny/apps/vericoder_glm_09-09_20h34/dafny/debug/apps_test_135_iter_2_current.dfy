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
lemma AllRemaindersDistinctIffNotHasNonDistinctRemainder(n: int, k: int)
    requires ValidInput(n, k)
    ensures AllRemaindersDistinct(n, k) <==> !HasNonDistinctRemainder(n, k)
{
    calc {
        AllRemaindersDistinct(n, k)
    <==>
        forall i :: 1 <= i <= k ==> n % i == (i - 1)
    <==>
        !(exists i :: 1 <= i <= k && n % i != (i - 1))
    <==>
        !HasNonDistinctRemainder(n, k)
    }
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
  if AllRemaindersDistinct(n, k) {
    return "Yes\n";
  } else {
    assert HasNonDistinctRemainder(n, k) by {
      AllRemaindersDistinctIffNotHasNonDistinctRemainder(n, k);
    }
    return "No\n";
  }
}
// </vc-code>

