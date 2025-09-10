predicate ValidInput(magnets: seq<string>)
{
    forall i :: 0 <= i < |magnets| ==> magnets[i] in {"01", "10"}
}

function CountGroups(magnets: seq<string>) : int
    requires ValidInput(magnets)
{
    if |magnets| == 0 then 0
    else 1 + |set i | 1 <= i < |magnets| && magnets[i] != magnets[i-1]|
}

// <vc-helpers>
function CountPrefix(magnets: seq<string>, k: int): int
    requires ValidInput(magnets)
    requires 0 <= k <= |magnets|
    decreases k
{
    if k == 0 then 0
    else if k == 1 then 1
    else CountPrefix(magnets, k-1) + (if magnets[k-1] != magnets[k-2] then 1 else 0)
}

lemma CountPrefixEqualsSet(magnets: seq<string>, k: int)
    requires ValidInput(magnets)
    requires 0 <= k <= |magnets|
    ensures CountPrefix(magnets,k) == (if k==0 then 0 else 1 + |set j | 1 <= j < k && magnets[j] != magnets[j-1]|)
    decreases k
{
    if k <= 1 {
        // k == 0 or k == 1: both sides match by definition
    } else {
        // Use induction hypothesis for k-1
        CountPrefixEqualsSet(magnets, k-1);

        var cond := magnets[k-1] != magnets[k-2];

        // Unfold definition of CountPrefix for k
        assert CountPrefix(magnets, k) == CountPrefix(magnets, k-1) + (if cond then 1 else 0);

        // From IH, k-1 >= 1, so CountPrefix(magnets, k-1) == 1 + |Sprev|
        // where Sprev = { j | 1 <= j < k-1 && magnets[j] != magnets[j-1] }
        var Sprev := set j | 1 <= j < k-1 && magnets[j] != magnets[j-1];
        var S := set j | 1 <= j < k && magnets[j] != magnets[j-1];

        // Sprev subset of S
        assert forall x :: x in Sprev ==> x in S;

        if cond {
            // k-1 is in S and not in Sprev
            assert (k-1) in S;
            assert (k-1) !in Sprev;

            // Any element in S but not in Sprev must be k-1
            assert forall y :: y in S && y !in Sprev ==> y == k-1;

            // Therefore S - Sprev == {k-1}
            assert S - Sprev == {k-1};

            // Cardinalities
            assert |S| == |Sprev| + 1;
        } else {
            // cond false => membership in S implies membership in Sprev
            assert forall y :: y in S ==> y in Sprev;
            assert S == Sprev;
            assert |S| == |Sprev|;
        }

        // Now combine equalities:
        // CountPrefix(magnets,k) == CountPrefix(magnets,k-1) + (if cond then 1 else 0)
        // == (1 + |Sprev|) + (if cond then 1 else 0) == 1 + |S|
        assert CountPrefix(magnets, k) == 1 + |S|;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(magnets: seq<string>) returns (result: int)
    requires ValidInput(magnets)
    ensures result >= 0
    ensures |magnets| == 0 ==> result == 0
    ensures |magnets| > 0 ==> result >= 1
    ensures result <= |magnets|
    ensures result == CountGroups(magnets)
// </vc-spec>
// <vc-code>
{
  if |magnets| == 0 {
    result := 0;
    return;
  }
  var n := |magnets|;
  result := 1;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant 1 <= result <= i
    invariant result == CountPrefix(magnets, i)
  {
    var changed := magnets[i] != magnets[i-1];
    if changed {
      result := result + 1;
    }
    // Relate CountPrefix at i+1 to i
    assert CountPrefix(magnets, i+1) == CountPrefix(magnets, i) + (if changed then 1 else 0);
    i := i + 1;
  }
  assert i == n;
  assert result == CountPrefix(magnets, n);
  CountPrefixEqualsSet(magnets, n);
  assert result == CountGroups(magnets);
}
// </vc-code>

