// <vc-preamble>
function bitwiseAnd(a: int, b: int): int
  requires a >= 0 && b >= 0
  ensures bitwiseAnd(a, b) >= 0
  ensures bitwiseAnd(a, b) <= a
  ensures bitwiseAnd(a, b) <= b
{
  if a == 0 || b == 0 then 0
  else if a % 2 == 1 && b % 2 == 1 then
    2 * bitwiseAnd(a / 2, b / 2) + 1
  else
    2 * bitwiseAnd(a / 2, b / 2)
}

predicate hasDuplicates(a: seq<int>)
{
  exists i, j :: 0 <= i < j < |a| && a[i] == a[j]
}

predicate canCreateDuplicatesWithOneOperation(a: seq<int>, x: int)
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  requires x >= 0
{
  exists i, j :: 0 <= i < |a| && 0 <= j < |a| && i != j &&
    bitwiseAnd(a[i], x) == a[j]
}

predicate canCreateDuplicatesWithTwoOperations(a: seq<int>, x: int)
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  requires x >= 0
{
  exists i, j :: 0 <= i < j < |a| && 
    bitwiseAnd(a[i], x) == bitwiseAnd(a[j], x)
}

predicate canCreateDuplicatesWithOperations(a: seq<int>, x: int, operations: int)
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  requires x >= 0
{
  operations >= 0 && 
  (operations == 0 ==> hasDuplicates(a)) &&
  (operations == 1 ==> canCreateDuplicatesWithOneOperation(a, x)) &&
  (operations == 2 ==> canCreateDuplicatesWithTwoOperations(a, x))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>, x: int) returns (result: int)
  requires |a| >= 2
  requires x >= 1
  requires forall i :: 0 <= i < |a| ==> a[i] >= 1
  requires forall i :: 0 <= i < |a| ==> a[i] <= 100000
  requires x <= 100000
  ensures result == -1 || (result >= 0 && result <= 2)
  ensures result == -1 ==> (forall operations :: 0 <= operations <= 2 ==> 
    !canCreateDuplicatesWithOperations(a, x, operations))
  ensures result >= 0 ==> canCreateDuplicatesWithOperations(a, x, result)
  ensures result >= 0 ==> (forall ops :: 0 <= ops < result ==> 
    !canCreateDuplicatesWithOperations(a, x, ops))
// </vc-spec>
// <vc-code>
{
  // Establish that a[i] >= 0 and x >= 0 for predicates
  assert forall i :: 0 <= i < |a| ==> a[i] >= 0;
  assert x >= 0;

  // Check for existing duplicates (0 operations)
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k1, k2 :: 0 <= k1 < k2 < i ==> a[k1] != a[k2]
  {
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant forall k :: 0 <= k < j ==> a[k] != a[i]
    {
      if a[j] == a[i] {
        assert hasDuplicates(a);
        return 0;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  assert !hasDuplicates(a);

  // Check for 1 operation possibility
  i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k :: 0 <= k < i ==> 
      (forall j :: 0 <= j < |a| && j != k ==> a[j] != bitwiseAnd(a[k], x))
  {
    assert a[i] >= 1 && x >= 1;
    var after_op := bitwiseAnd(a[i], x);
    var j := 0;
    while j < |a|
      invariant 0 <= j <= |a|
      invariant forall k :: 0 <= k < j && k != i ==> a[k] != after_op
    {
      if i != j && a[j] == after_op {
        assert canCreateDuplicatesWithOneOperation(a, x);
        return 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  assert !canCreateDuplicatesWithOneOperation(a, x);

  // Check for 2 operations possibility
  var after_ops := [];
  i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |after_ops| == i
    invariant forall k :: 0 <= k < i ==> after_ops[k] == bitwiseAnd(a[k], x)
  {
    assert a[i] >= 1 && x >= 1;
    after_ops := after_ops + [bitwiseAnd(a[i], x)];
    i := i + 1;
  }

  i := 0;
  while i < |after_ops|
    invariant 0 <= i <= |after_ops|
    invariant forall k1, k2 :: 0 <= k1 < k2 < i ==> after_ops[k1] != after_ops[k2]
  {
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant forall k :: 0 <= k < j ==> after_ops[k] != after_ops[i]
    {
      if after_ops[j] == after_ops[i] {
        assert canCreateDuplicatesWithTwoOperations(a, x);
        return 2;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  assert !canCreateDuplicatesWithTwoOperations(a, x);

  result := -1;
}
// </vc-code>
