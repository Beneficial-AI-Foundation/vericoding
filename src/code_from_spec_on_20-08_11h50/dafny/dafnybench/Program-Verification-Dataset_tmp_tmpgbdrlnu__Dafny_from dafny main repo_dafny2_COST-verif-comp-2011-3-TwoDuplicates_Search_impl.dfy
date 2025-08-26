lemma IsPrefixDuplicateExtension(a: seq<int>, i: int, x: int)
  requires 0 <= i < |a|
  requires IsPrefixDuplicate(a, i, x)
  ensures IsPrefixDuplicate(a, i+1, x)
{
  // If x is a prefix duplicate up to i, it remains so up to i+1
}

lemma NewDuplicateFound(a: seq<int>, i: int, x: int)
  requires 0 <= i < |a|
  requires a[i] == x
  requires IsPrefixDuplicate(a, i, x)
  ensures IsDuplicate(a, x)
{
  // If we see x at position i and it was already a prefix duplicate, then it's a full duplicate
}

// Helper predicates and lemmas

predicate IsPrefixDuplicate(a: seq<int>, i: int, x: int)
{
  exists j, k :: 0 <= j < k < i && a[j] == x && a[k] == x
}

predicate IsDuplicate(a: seq<int>, x: int)
{
  exists j, k :: 0 <= j < k < |a| && a[j] == x && a[k] == x
}

lemma PrefixDuplicateImpliesDuplicate(a: seq<int>, i: int, x: int)
  requires 0 <= i < |a|
  requires a[i] == x
  requires IsPrefixDuplicate(a, i, x)
  ensures IsDuplicate(a, x)
{
  var prefix := a[..i];
  assert exists j, k :: 0 <= j < k < i && a[j] == x && a[k] == x;
  var j, k :| 0 <= j < k < i && a[j] == x && a[k] == x;
  assert a[j] == x && a[k] == x && a[i] == x;
  assert 0 <= j < k < i < |a|;
  // We have x at positions j, k, and i, so it's a duplicate
}

lemma SeenImpliesPrefixDuplicate(a: seq<int>, i: int, val: int)
  requires 0 <= i < |a|
  requires a[i] == val
  requires exists j :: 0 <= j < i && a[j] == val
  ensures IsPrefixDuplicate(a, i+1, val)
{
  var j :| 0 <= j < i && a[j] == val;
  assert a[j] == val && a[i] == val;
  assert 0 <= j < i < i+1;
}

method FindTwoDuplicates(a: array<int>, n: int) returns (p: int, q: int)
  requires a.Length > 0
  requires n > 0
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i] < n
  requires exists x :: IsDuplicate(a[..], x)
  requires exists x, y :: x != y && IsDuplicate(a[..], x) && IsDuplicate(a[..], y)
  ensures p != q
  ensures 0 <= p < n && 0 <= q < n
  ensures IsDuplicate(a[..], p) && IsDuplicate(a[..], q)
{
  p := -1;
  q := -1;
  var seen := new bool[n];
  var i := 0;
  
  // Initialize seen array
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> !seen[k]
  {
    seen[i] := false;
    i := i + 1;
  }
  
  i := 0;
  
  while i < a.Length && (p == -1 || q == -1 || p == q)
    invariant 0 <= i <= a.Length
    invariant seen.Length == n
    invariant forall k :: 0 <= k < seen.Length ==> (seen[k] <==> (exists j :: 0 <= j < i && a[j] == k))
    invariant p == -1 || (0 <= p < n && IsDuplicate(a[..], p))
    invariant q == -1 || (0 <= q < n && IsDuplicate(a[..], q))
    invariant p != -1 && q != -1 && p != q ==> IsDuplicate(a[..], p) && IsDuplicate(a[..], q)
    decreases a.Length - i
  {
    var val := a[i];
    
    if seen[val] {
      // Found a duplicate - val appears again
      assert exists j :: 0 <= j < i && a[j] == val;
      var j :| 0 <= j < i && a[j] == val;
      assert a[j] == val && a[i] == val && j < i;
      assert IsDuplicate(a[..], val);
      
      if p == -1 {
        // First duplicate found
        p := val;
      } else if q == -1 && val != p {
        // Second distinct duplicate found
        q := val;
      } else if q == -1 {
        // Same duplicate as p, keep looking
        // q remains -1
      } else if val != p && val != q {
        // Found a third distinct duplicate, we can use any two
        q := val;
      }
    } else {
      seen[val] := true;
    }
    
    i := i + 1;
  }
  
  // At this point, we should have found two distinct duplicates
  assert p != -1 && q != -1 && p != q;
  assert IsDuplicate(a[..], p) && IsDuplicate(a[..], q);
}