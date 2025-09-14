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
lemma All_implies_notHas(n: int, k: int)
  requires ValidInput(n, k)
  requires AllRemaindersDistinct(n, k)
  ensures !HasNonDistinctRemainder(n, k)
{
  assert (forall i :: 1 <= i <= k ==> n % i == i - 1);
  assert !(exists i :: 1 <= i <= k && n % i != i - 1);
}

lemma NotAll_implies_Has(n: int, k: int)
  requires ValidInput(n, k)
  requires !AllRemaindersDistinct(n, k)
  ensures HasNonDistinctRemainder(n, k)
{
  assert !(forall i :: 1 <= i <= k ==> n % i == i - 1);
  assert (exists i :: 1 <= i <= k && n % i != i - 1);
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
    result := "Yes\n";
    All_implies_notHas(n, k);
  } else {
    result := "No\n";
    NotAll_implies_Has(n, k);
  }
}
// </vc-code>

