predicate ValidInput(n: int, m: seq<int>) {
    n > 0 && |m| == n && 
    forall i :: 0 <= i < n ==> 0 <= m[i] < i + 1
}

predicate ValidSolution(n: int, m: seq<int>, dm: seq<int>) {
    |dm| == n && |m| == n &&
    (forall i :: 0 <= i < n ==> dm[i] >= m[i] + 1) &&
    (forall i :: 0 <= i < n - 1 ==> dm[i] <= dm[i + 1])
}

function SumBelow(m: seq<int>, dm: seq<int>): int
    requires |m| == |dm|
{
    if |m| == 0 then 0
    else (dm[0] - 1 - m[0]) + SumBelow(m[1..], dm[1..])
}

// <vc-helpers>
lemma SumBelowNonNegative(m: seq<int>, dm: seq<int>)
  requires |m| == |dm|
  requires forall i :: 0 <= i < |m| ==> dm[i] >= m[i] + 1
  requires forall i :: 0 <= i < |m| - 1 ==> dm[i] <= dm[i + 1]
  ensures SumBelow(m, dm) >= 0
{
  if |m| > 0 {
    var inner_m := m[1..];
    var inner_dm := dm[1..];
    
    assert dm[0] - 1 - m[0] >= 0;
    
    SumBelowNonNegative(inner_m, inner_dm);
  }
}

function max(a: int, b: int): int
{
  if a >= b then a else b
}

lemma SumBelowRecursive(m: seq<int>, dm: seq<int>)
  requires |m| == |dm|
  ensures SumBelow(m, dm) == (if |m| == 0 then 0 else (dm[0] - 1 - m[0]) + SumBelow(m[1..], dm[1..]))
{
  // This lemma is trivial since SumBelow is defined recursively
}

lemma SumBelowSingleElement(m: seq<int>, dm: seq<int>)
  requires |m| == 1 && |dm| == 1
  requires dm[0] >= m[0] + 1
  ensures SumBelow(m, dm) >= 0
{
  assert SumBelow(m, dm) == dm[0] - 1 - m[0];
}

lemma SumBelowPreservesInvariant(m1: seq<int>, dm1: seq<int>, m2: seq<int>, dm2: seq<int>)
  requires |m1| == |dm1| && |m2| == |dm2|
  requires m1 == m2[0..|m1|]
  requires dm1 == dm2[0..|dm1|]
  ensures SumBelow(m2, dm2) == SumBelow(m1, dm1) + SumBelow(m2[|m1|..], dm2[|dm1|..])
{
  if |m1| == 0 {
    assert m1 == [] && dm1 == [];
    assert SumBelow(m2, dm2) == SumBelow([], []) + SumBelow(m2, dm2);
  } else {
    var head_m1 := m1[0];
    var head_dm1 := dm1[0];
    var tail_m1 := m1[1..];
    var tail_dm1 := dm1[1..];
    
    calc {
      SumBelow(m2, dm2);
      == { SumBelowRecursive(m2, dm2); }
      (dm2[0] - 1 - m2[0]) + SumBelow(m2[1..], dm2[1..]);
      == { assert m2[0] == head_m1 && dm2[0] == head_dm1; }
      (head_dm1 - 1 - head_m1) + SumBelow(m2[1..], dm2[1..]);
      == { SumBelowRecursive(m1, dm1); }
      (SumBelow(m1, dm1) - SumBelow(tail_m1, tail_dm1)) + SumBelow(m2[1..], dm2[1..]);
    }
    
    SumBelowPreservesInvariant(tail_m1, tail_dm1, m2[1..], dm2[1..]);
  }
}

lemma SumBelowSliceUpdate(m: seq<int>, dm: seq<int>, i: int, new_val: int)
  requires 0 <= i < |m| && |m| == |dm|
  ensures SumBelow(m, dm[0..i] + [new_val] + dm[i+1..]) == 
           SumBelow(m[0..i], dm[0..i]) + (new_val - 1 - m[i]) + SumBelow(m[i+1..], dm[i+1..])
{
  if i == 0 {
    assert |m| > 0;
    SumBelowRecursive(m, dm[0..i] + [new_val] + dm[i+1..]);
  } else {
    var prefix := dm[0..i] + [new_val] + dm[i+1..];
    SumBelowRecursive(m, prefix);
    SumBelowRecursive(m[0..i], prefix[0..i]);
    SumBelowRecursive(m[i+1..], prefix[i+1..]);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: seq<int>) returns (result: int)
    requires ValidInput(n, m)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  var dm := new int[n];
  var sum := 0;
  
  var i := 0;
  var prev_dm := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant dm.Length == n
    invariant forall j :: 0 <= j < i ==> dm[j] >= m[j] + 1
    invariant forall j :: 0 <= j < i - 1 ==> dm[j] <= dm[j + 1]
    invariant forall j :: 0 <= j < i ==> dm[j] >= prev_dm
    invariant prev_dm == (if i > 0 then dm[i-1] else 0)
    invariant sum == SumBelow(m[0..i], dm[0..i])
    invariant sum >= 0
  {
    if i == 0 {
      dm[i] := m[i] + 1;
    } else {
      dm[i] := max(m[i] + 1, dm[i-1]);
    }
    
    assert dm[i] >= m[i] + 1;
    assert i == 0 || dm[i] >= dm[i-1];
    
    // Update sum using the correct SumBelow relationship
    var old_dm_i_slice := dm[0..i];
    var old_sum := sum;
    
    // Calculate new sum by reconstructing the SumBelow value
    if i == 0 {
      sum := dm[i] - 1 - m[i];
    } else {
      sum := SumBelow(m[0..i-1], dm[0..i-1]) + (dm[i] - 1 - m[i]);
    }
    
    assert sum == SumBelow(m[0..i], dm[0..i]);
    
    // Prove sum >= 0
    if i > 0 {
      SumBelowNonNegative(m[0..i-1], dm[0..i-1]);
    }
    assert dm[i] - 1 - m[i] >= 0;
    
    prev_dm := dm[i];
    i := i + 1;
  }
  
  result := sum;
}
// </vc-code>

