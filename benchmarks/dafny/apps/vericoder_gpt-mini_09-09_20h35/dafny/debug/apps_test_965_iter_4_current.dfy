predicate ValidInput(n: int, statuses: string)
{
    n >= 2 && |statuses| == n && 
    forall i :: 0 <= i < |statuses| ==> statuses[i] in {'A', 'I', 'F'}
}

function CountStatus(statuses: string, status: char): int
{
    |set i | 0 <= i < |statuses| && statuses[i] == status|
}

function ExpectedResult(statuses: string): int
{
    var cnt_I := CountStatus(statuses, 'I');
    var cnt_A := CountStatus(statuses, 'A');
    if cnt_I == 0 then cnt_A
    else if cnt_I == 1 then 1
    else 0
}

// <vc-helpers>
function CountPrefix(statuses: string, k: int, status: char): int
  requires 0 <= k <= |statuses|
{
  if k == 0 then 0 else CountPrefix(statuses, k-1, status) + (if statuses[k-1] == status then 1 else 0)
}

lemma CountPrefixEqualsSet(statuses: string, k: int, status: char)
  requires 0 <= k <= |statuses|
  ensures CountPrefix(statuses, k, status) == |(set i | 0 <= i < k && statuses[i] == status)|
{
  if k == 0 {
    // base case: both are 0 / empty
  } else {
    CountPrefixEqualsSet(statuses, k-1, status);
    assert CountPrefix(statuses, k, status) == CountPrefix(statuses, k-1, status) + (if statuses[k-1] == status then 1 else 0);
    var Sprev := (set i | 0 <= i < k-1 && statuses[i] == status);
    var Scurr := (set i | 0 <= i < k && statuses[i] == status);
    assert CountPrefix(statuses, k-1, status) == |Sprev|;
    if statuses[k-1] == status {
      assert Scurr == Sprev + {k-1};
      assert not (k-1 in Sprev);
      assert |Scurr| == |Sprev| + |{k-1}|;
      assert |{k-1}| == 1;
      assert CountPrefix(statuses, k, status) == |Scurr|;
    } else {
      assert Scurr == Sprev;
      assert |Scurr| == |Sprev|;
      assert CountPrefix(statuses, k, status) == |Scurr|;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, statuses: string) returns (result: int)
    requires ValidInput(n, statuses)
    ensures result == ExpectedResult(statuses)
// </vc-spec>
// <vc-code>
{
  var cntA := 0;
  var cntI := 0;
  var i := 0;
  while i < |statuses|
    invariant 0 <= i <= |statuses|
    invariant cntA == CountPrefix(statuses, i, 'A')
    invariant cntI == CountPrefix(statuses, i, 'I')
  {
    var oldCntA := cntA;
    var oldCntI := cntI;
    assert oldCntA == CountPrefix(statuses, i, 'A');
    assert oldCntI == CountPrefix(statuses, i, 'I');
    if statuses[i] == 'A' {
      cntA := cntA + 1;
    } else if statuses[i] == 'I' {
      cntI := cntI + 1;
    }
    if statuses[i] == 'A' {
      assert cntA == oldCntA + 1;
    } else {
      assert cntA == oldCntA;
    }
    if statuses[i] == 'I' {
      assert cntI == oldCntI + 1;
    } else {
      assert cntI == oldCntI;
    }
    assert CountPrefix(statuses, i+1, 'A') == CountPrefix(statuses, i, 'A') + (if statuses[i] == 'A' then 1 else 0);
    assert CountPrefix(statuses, i+1, 'I') == CountPrefix(statuses, i, 'I') + (if statuses[i] == 'I' then 1 else 0);
    assert cntA == CountPrefix(statuses, i+1, 'A');
    assert cntI == CountPrefix(statuses, i+1, 'I');
    i := i + 1;
  }

  // Relate the counted prefixes at full length to the specification's CountStatus
  CountPrefixEqualsSet(statuses, |statuses|, 'A');
  CountPrefixEqualsSet(statuses, |statuses|, 'I');
  assert cntA == CountPrefix(statuses, |statuses|, 'A');
  assert cntI == CountPrefix(statuses, |statuses|, 'I');
  assert cntA == CountStatus(statuses, 'A');
  assert cntI == CountStatus(statuses, 'I');

  if cntI == 0 {
    result := cntA;
  } else if cntI == 1 {
    result := 1;
  } else {
    result := 0;
  }
}
// </vc-code>

