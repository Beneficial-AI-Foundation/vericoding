// <vc-preamble>
function MultisetCount<T(==)>(s: seq<T>, x: T): nat
{
    |set i | 0 <= i < |s| && s[i] == x|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed equality proofs with explicit set decomposition */
lemma MultisetPreservedBySwap<T>(s: seq<T>, i: int, j: int, x: T)
  requires 0 <= i < |s| && 0 <= j < |s|
  ensures MultisetCount(s[i := s[j]][j := s[i]], x) == MultisetCount(s, x)
{
  var s' := s[i := s[j]][j := s[i]];
  
  if i == j {
    return;
  }
  
  var orig_set := set k | 0 <= k < |s| && s[k] == x;
  var new_set := set k | 0 <= k < |s'| && s'[k] == x;
  
  // Decompose original set
  var orig_without_ij := set k | 0 <= k < |s| && k != i && k != j && s[k] == x;
  var orig_i := if s[i] == x then {i} else {};
  var orig_j := if s[j] == x then {j} else {};
  
  // Decompose new set  
  var new_without_ij := set k | 0 <= k < |s'| && k != i && k != j && s'[k] == x;
  var new_i := if s'[i] == x then {i} else {};
  var new_j := if s'[j] == x then {j} else {};
  
  // Prove the decompositions are equal
  assert orig_set == orig_without_ij + orig_i + orig_j;
  assert new_set == new_without_ij + new_i + new_j;
  assert orig_without_ij == new_without_ij;
  
  // Since s'[i] == s[j] and s'[j] == s[i], the sets are equal
  assert new_i == (if s[j] == x then {i} else {});
  assert new_j == (if s[i] == x then {j} else {});
  assert orig_i + orig_j == new_i + new_j;
  
  assert orig_set == new_set;
}

lemma MultisetPreservedByCopy<T>(s1: seq<T>, s2: seq<T>, x: T)
  requires |s1| == |s2|
  requires forall k :: 0 <= k < |s1| ==> s1[k] == s2[k]
  ensures MultisetCount(s1, x) == MultisetCount(s2, x)
{
  assert (set k | 0 <= k < |s1| && s1[k] == x) == (set k | 0 <= k < |s2| && s2[k] == x);
}
// </vc-helpers>

// <vc-spec>
method Sort(a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length &&
        (forall i, j :: 0 <= i < j < result.Length ==> result[i] <= result[j]) &&
        (forall x :: MultisetCount(result[..], x) == MultisetCount(a[..], x))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed snapshot references and added proper modifies clauses */
  result := new int[a.Length];
  if a.Length == 0 {
    return;
  }
  
  // Copy array elements
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> result[k] == a[k]
  {
    result[i] := a[i];
  }
  
  // Prove multiset equality after copying
  forall x {
    MultisetPreservedByCopy(result[..], a[..], x);
  }
  
  // Selection sort
  for i := 0 to result.Length
    invariant 0 <= i <= result.Length
    invariant forall k, l :: 0 <= k < l < i ==> result[k] <= result[l]
    invariant forall k :: 0 <= k < i ==> forall l :: i <= l < result.Length ==> result[k] <= result[l]
    invariant forall x :: MultisetCount(result[..], x) == MultisetCount(a[..], x)
    modifies result
  {
    var minIdx := i;
    for j := i + 1 to result.Length
      invariant i <= minIdx < result.Length
      invariant i <= j <= result.Length
      invariant forall k :: i <= k < j ==> result[minIdx] <= result[k]
    {
      if j < result.Length && result[j] < result[minIdx] {
        minIdx := j;
      }
    }
    if minIdx != i {
      var oldSeq := result[..];
      var temp := result[i];
      result[i] := result[minIdx];
      result[minIdx] := temp;
      
      forall x {
        MultisetPreservedBySwap(oldSeq, i, minIdx, x);
      }
    }
  }
}
// </vc-code>
