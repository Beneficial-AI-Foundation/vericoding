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
lemma ExistsIffNotForall(n: int, k: int)
    requires ValidInput(n, k)
    ensures HasNonDistinctRemainder(n, k) <==> !AllRemaindersDistinct(n, k)
{
    assert HasNonDistinctRemainder(n, k) <==> (exists i :: 1 <= i <= k && n % i != (i - 1));
    assert AllRemaindersDistinct(n, k) <==> (forall i :: 1 <= i <= k ==> n % i == (i - 1));
    assert (exists i :: 1 <= i <= k && n % i != (i - 1)) <==> !(forall i :: 1 <= i <= k ==> n % i == (i - 1));
    assert HasNonDistinctRemainder(n, k) <==> !AllRemaindersDistinct(n, k);
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
  assert AllRemaindersDistinct(n, k) <==> (forall i :: 1 <= i <= k ==> n % i == (i - 1));
  assert HasNonDistinctRemainder(n, k) <==> (exists i :: 1 <= i <= k && n % i != (i - 1));
  assert (exists i :: 1 <= i <= k && n % i != (i - 1)) <==> !(forall i :: 1 <= i <= k ==> n % i == (i - 1));
  if (exists i :: 1 <= i <= k && n % i != (i - 1)) {
    result := "No\n";
  } else {
    result := "Yes\n";
  }
}
// </vc-code>

