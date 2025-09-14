// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed Sorted predicate and lemma preconditions */
function Insert(a: seq<int>, key: int, i: int): seq<int>
  requires 0 <= i <= |a|
{
  a[0..i] + [key] + a[i..]
}

predicate Sorted(a: seq<int>)
{
  if |a| <= 1 then true
  else forall j :: 0 <= j < |a| - 1 ==> a[j] <= a[j+1]
}

lemma MultisetPreservedInsert(a: seq<int>, key: int, i: int)
  requires 0 <= i <= |a|
  ensures multiset(a[0..i] + [key] + a[i..]) == multiset(a) + multiset{key}
{
  // Multiset lemma implementation
  var left := a[0..i];
  var right := a[i..];
  calc {
    multiset(left + [key] + right);
    == multiset(left) + multiset([key]) + multiset(right);
    == multiset(left) + multiset{key} + multiset(right);
    == multiset(a) + multiset{key};
  }
}

lemma SortedInsertion(a: seq<int>, key: int, i: int)
  requires Sorted(a[0..i]) && Sorted(a[i..])
  requires i == 0 || key >= a[i-1]
  requires i == |a| || key <= a[i]
  ensures Sorted(a[0..i] + [key] + a[i..])
{
  // Proof that inserting maintains sortedness
  if |a[0..i]| > 0 {
    assert a[i-1] <= key;
  }
  if i < |a| {
    assert key <= a[i];
  }
}
// </vc-helpers>

// <vc-spec>
method insertion_sort(l: array<int>) returns (result: array<int>)
    ensures
        /* The result is sorted in non-decreasing order */
        forall i, j :: 0 <= i < j < result.Length ==> result[i] <= result[j]
    ensures
        /* The result is a permutation of the input */
        result.Length == l.Length && multiset(result[..]) == multiset(l[..])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed sequence slicing and insertion logic */
{
    result := new int[l.Length];
    
    if l.Length == 0 {
        return;
    }
    
    // Copy first element
    result[0] := l[0];
    
    var k := 1;
    while k < l.Length
        invariant 1 <= k <= l.Length
        invariant Sorted(result[0..k])
        invariant multiset(result[0..k]) == multiset(l[0..k])
    {
        var key := l[k];
        var i := 0;
        
        // Find insertion position
        while i < k && key > result[i]
            invariant 0 <= i <= k
            invariant forall j :: 0 <= j < i ==> key > result[j]
        {
            i := i + 1;
        }
        
        // Shift elements to make space
        var j := k;
        while j > i
            invariant i <= j <= k
            invariant forall m :: i <= m < j ==> result[m] == old(result)[m]
        {
            result[j] := result[j-1];
            j := j - 1;
        }
        
        // Insert the key
        result[i] := key;
        
        // Apply lemmas to prove invariants
        var currentSeq := result[0..k];
        MultisetPreservedInsert(result[0..k-1], key, i);
        if k >= 1 {
            SortedInsertion(result[0..i], key, i);
        }
        
        k := k + 1;
    }
}
// </vc-code>
