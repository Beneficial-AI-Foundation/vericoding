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
lemma ForallToAllRemainders(n: int, k: int)
    requires ValidInput(n, k)
    requires forall j :: 1 <= j <= k ==> n % j == j - 1
    ensures AllRemaindersDistinct(n, k)
{
    // The predicate AllRemaindersDistinct is exactly the forall above,
    // so this follows directly.
    assert forall j :: 1 <= j <= k ==> n % j == j - 1;
    assert AllRemaindersDistinct(n, k);
}

lemma WitnessImpliesHasNonDistinct(n: int, k: int, w: int)
    requires ValidInput(n, k)
    requires 1 <= w <= k
    requires n % w != w - 1
    ensures HasNonDistinctRemainder(n, k)
{
    // Provide the witness for the existential in HasNonDistinctRemainder
    assert 1 <= w <= k;
    assert n % w != w - 1;
    assert exists i :: 1 <= i <= k && n % i != i - 1;
    assert HasNonDistinctRemainder(n, k);
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
  var good := true;
  var w := 0;
  while i <= k
    invariant 1 <= i && i <= k + 1
    invariant good ==> (forall j :: 1 <= j < i ==> n % j == j - 1)
    invariant (forall j :: 1 <= j < i ==> n % j == j - 1) ==> good
    invariant w == 0 ==> good
    invariant good ==> w == 0
    invariant (w != 0) ==> (1 <= w && w < i && n % w != w - 1)
  {
    var cond := n % i == i - 1;
    if !cond && w == 0 {
      w := i;
    }
    good := good && cond;
    i := i + 1;
  }

  if good {
    ForallToAllRemainders(n, k);
    return "Yes\n";
  } else {
    assert w != 0;
    // After loop i == k+1, so w < i implies w <= k
    assert 1 <= w && w <= k;
    WitnessImpliesHasNonDistinct(n, k, w);
    return "No\n";
  }
}
// </vc-code>

