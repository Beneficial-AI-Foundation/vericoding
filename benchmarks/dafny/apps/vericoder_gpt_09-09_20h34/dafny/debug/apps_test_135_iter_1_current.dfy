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
    assert HasNonDistinctRemainder(n, k) ==> !AllRemaindersDistinct(n, k);
    assert !AllRemaindersDistinct(n, k) ==> HasNonDistinctRemainder(n, k);
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
  call ExistsIffNotForall(n, k);
  if AllRemaindersDistinct(n, k) {
    result := "Yes\n";
    assert !HasNonDistinctRemainder(n, k);
  } else {
    result := "No\n";
    assert HasNonDistinctRemainder(n, k);
  }
}
// </vc-code>

