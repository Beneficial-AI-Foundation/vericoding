

// <vc-helpers>
predicate IsMinHeapNode(a: array<int>, i: int)
  requires a != null
  requires 0 <= i < a.Length / 2
  reads a
{
  a[i] <= a[2*i + 1] && (2*i + 2 >= a.Length || a[i] <= a[2*i + 2])
}

lemma IsMinHeapLemma(a: array<int>, i: int)
  requires a != null
  requires 0 <= i < a.Length / 2
  ensures IsMinHeapNode(a, i) <==> 
           (a[i] <= a[2*i + 1] && (2*i + 2 >= a.Length || a[i] <= a[2*i + 2]))
{
}

lemma IsMinHeapNodeImpliesConjuncts(a: array<int>, i: int)
  requires a != null
  requires 0 <= i < a.Length / 2
  requires IsMinHeapNode(a, i)
  ensures a[i] <= a[2*i + 1] && (2*i + 2 >= a.Length || a[i] <= a[2*i + 2])
{
}
// </vc-helpers>

// <vc-spec>
method IsMinHeap(a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length / 2 ==> a[i] <= a[2*i + 1] && (2*i + 2 == a.Length || a[i] <= a[2*i + 2])
    ensures !result ==> exists i :: 0 <= i < a.Length / 2 && (a[i] > a[2*i + 1] || (2*i + 2 != a.Length && a[i] > a[2*i + 2]))
// </vc-spec>
// <vc-code>
{
  var idx := 0;
  result := true;
  
  while idx < a.Length / 2
    invariant 0 <= idx <= a.Length / 2
    invariant result ==> forall j :: 0 <= j < idx ==> IsMinHeapNode(a, j)
    invariant !result ==> exists j :: 0 <= j < idx && (a[j] > a[2*j + 1] || (2*j + 2 < a.Length && a[j] > a[2*j + 2]))
    decreases a.Length / 2 - idx
  {
    if 2*idx + 1 < a.Length && a[idx] > a[2*idx + 1] {
      result := false;
    } else if 2*idx + 2 < a.Length && a[idx] > a[2*idx + 2] {
      result := false;
    }
    
    if !result {
      // We found a violation, can return immediately
      return;
    } else {
      // Prove that this node satisfies the heap property
      idx := idx + 1;
    }
  }
}
// </vc-code>

