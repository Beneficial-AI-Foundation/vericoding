lemma InsertPreservesPositive(a_prefix: seq<int>, key: int, a_suffix: seq<int>)
  requires forall i :: 0 <= i < |a_prefix| ==> a_prefix[i] > 0
  requires forall i :: 0 <= i < |a_suffix| ==> a_suffix[i] > 0
  requires key > 0
  ensures forall i :: 0 <= i < |a_prefix + [key] + a_suffix| ==> (a_prefix + [key] + a_suffix)[i] > 0
{
  var result := a_prefix + [key] + a_suffix;
  assert forall i :: 0 <= i < |a_prefix| ==> result[i] == a_prefix[i] && result[i] > 0;
  assert result[|a_prefix|] == key && key > 0;
  assert forall i :: |a_prefix| + 1 <= i < |result| ==> result[i] == a_suffix[i - |a_prefix| - 1] && result[i] > 0;
}

lemma InsertPreservesSorted(a_prefix: seq<int>, key: int, a_suffix: seq<int>)
  requires sorted(a_prefix + a_suffix)
  requires |a_prefix| > 0 ==> a_prefix[|a_prefix|-1] < key
  requires |a_suffix| > 0 ==> key < a_suffix[0]
  ensures sorted(a_prefix + [key] + a_suffix)
{
  var result := a_prefix + [key] + a_suffix;
  var orig := a_prefix + a_suffix;
  
  forall i, j | 0 <= i < j < |result|
    ensures result[i] < result[j]
  {
    if j < |a_prefix| {
      // Both in prefix
      assert result[i] == a_prefix[i] && result[j] == a_prefix[j];
    } else if i < |a_prefix| && j == |a_prefix| {
      // i in prefix, j is key
      assert result[i] == a_prefix[i] && result[j] == key;
    } else if i < |a_prefix| && j > |a_prefix| {
      // i in prefix, j in suffix
      assert result[i] == a_prefix[i] && result[j] == a_suffix[j - |a_prefix| - 1];
      // Need to prove a_prefix[i] < a_suffix[j - |a_prefix| - 1]
      if |a_prefix| > 0 && |a_suffix| > 0 {
        assert a_prefix[i] < a_prefix[|a_prefix| - 1] < key < a_suffix[0] <= a_suffix[j - |a_prefix| - 1];
      }
    } else if i == |a_prefix| && j > |a_prefix| {
      // i is key, j in suffix
      assert result[i] == key && result[j] == a_suffix[j - |a_prefix| - 1];
    } else {
      // Both in suffix
      assert result[i] == a_suffix[i - |a_prefix| - 1] && result[j] == a_suffix[j - |a_prefix| - 1];
    }
  }
}

lemma DistributiveIn(orig: seq<int>, result: seq<int>, idx: int, key: int)
  requires 0 <= idx < |result|
  requires |result| == |orig| + 1
  requires result[idx] == key
  requires forall i :: 0 <= i < idx ==> result[i] == orig[i]
  requires forall i :: idx < i < |result| ==> result[i] == orig[i-1]
  ensures forall x :: x in orig ==> x in result
  ensures key in result
{
  forall x | x in orig
    ensures x in result
  {
    var j :| 0 <= j < |orig| && orig[j] == x;
    if j < idx {
      assert result[j] == orig[j] == x;
    } else {
      assert result[j + 1] == orig[j] == x;
    }
  }
  assert key in result;
}

predicate sorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}

method GetInsertIndex(a: array<int>, limit: int, key: int) returns (idx: int)
  requires 0 <= limit < a.Length
  requires sorted(a[..limit])
  requires forall i :: 0 <= i < limit ==> a[i] > 0
  requires key > 0
  ensures 0 <= idx <= limit
  ensures forall i :: 0 <= i < idx ==> a[i] < key
  ensures forall i :: idx <= i < limit ==> a[i] > key
{
  idx := 0;
  while idx < limit && a[idx] < key
    invariant 0 <= idx <= limit
    invariant forall i :: 0 <= i < idx ==> a[i] < key
  {
    idx := idx + 1;
  }
  assert forall i :: idx <= i < limit ==> a[i] >= key;
  assert forall i :: idx <= i < limit ==> a[i] != key;
  assert forall i :: idx <= i < limit ==> a[i] > key;
}

method InsertIntoSorted(a: array<int>, limit: int, key: int) returns (b: array<int>)
  requires 0 <= limit < a.Length
  requires sorted(a[..limit])
  requires forall i :: 0 <= i < limit ==> a[i] > 0
  requires forall i :: limit <= i < a.Length ==> a[i] == 0
  requires key > 0
  ensures b.Length == a.Length
  ensures sorted(b[..limit+1])
  ensures forall i :: 0 <= i < limit + 1 ==> b[i] > 0
  ensures forall i :: limit + 1 <= i < b.Length ==> b[i] == 0
  ensures forall x :: x in a[..limit] ==> x in b[..limit+1]
  ensures key in b[..limit+1]
{
  var idx := GetInsertIndex(a, limit, key);
  b := new int[a.Length];
  
  // Copy prefix (elements before insertion point)
  for i := 0 to idx
    invariant forall j :: 0 <= j < i ==> b[j] == a[j]
  {
    b[i] := a[i];
  }
  
  // Insert the key
  b[idx] := key;
  
  // Copy suffix (elements after insertion point)
  for i := idx to limit
    invariant forall j :: 0 <= j < idx ==> b[j] == a[j]
    invariant b[idx] == key
    invariant forall j :: idx + 1 <= j <= i ==> b[j] == a[j - 1]
  {
    b[i + 1] := a[i];
  }
  
  // Set remaining elements to 0
  for i := limit + 1 to b.Length
    invariant forall j :: limit + 1 <= j < i ==> b[j] == 0
  {
    b[i] := 0;
  }
  
  // Prove that the result is equivalent to prefix + [key] + suffix
  ghost var a_prefix := a[..idx];
  ghost var a_suffix := a[idx..limit];
  ghost var expected := a_prefix + [key] + a_suffix;
  
  // Prove structural equivalence step by step
  forall i | 0 <= i < limit + 1
    ensures b[i] == expected[i]
  {
    if i < idx {
      assert b[i] == a[i] == a_prefix[i] == expected[i];
    } else if i == idx {
      assert b[i] == key == expected[i];
    } else {
      assert b[i] == a[i - 1] == a_suffix[i - idx - 1] == expected[i];
    }
  }
  assert b[..limit+1] == expected;
  
  // Apply lemmas to prove postconditions
  InsertPreservesPositive(a_prefix, key, a_suffix);
  InsertPreservesSorted(a_prefix, key, a_suffix);
  
  // Prove membership
  DistributiveIn(a[..limit], b[..limit+1], idx, key);
}