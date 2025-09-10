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
  ghost var witness: int := 0;
  while i <= k
    invariant 1 <= i <= k + 1
    invariant good <==> (forall j :: 1 <= j < i ==> n % j == j - 1)
    invariant (witness == 0) <==> good
    invariant (witness != 0) ==> (1 <= witness < i && n % witness != witness - 1)
  {
    var cond := n % i == i - 1;
    if !cond && witness == 0 {
      witness := i;
    }
    good := good && cond;
    i := i + 1;
  }

  // After the loop, i == k+1 and good <==> forall j in 1..k :: n%j == j-1
  if good {
    // From the forall we can conclude the predicate
    ForallToAllRemainders(n, k);
    return "Yes\n";
  } else {
    // witness is a valid index demonstrating the failure
    WitnessImpliesHasNonDistinct(n, k, witness);
    return "No\n";
  }
}
// </vc-code>

