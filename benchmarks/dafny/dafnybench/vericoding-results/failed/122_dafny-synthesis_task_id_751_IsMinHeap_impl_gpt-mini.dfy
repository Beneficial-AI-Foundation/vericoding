

// <vc-helpers>
lemma ViolationImpliesExists(a: array<int>, i:int, n:int)
  requires a != null
  requires 0 <= i < n/2
  requires 2*i+1 < n
  requires a[i] > a[2*i+1] || (2*i+2 < n && a[i] > a[2*i+2])
  ensures exists k :: 0 <= k < n/2 && (a[k] > a[2*k + 1] || (2*k + 2 < n && a[k] > a[2*k + 2]))
{
  assert 0 <= i < n/2 && (a[i] > a[2*i+1] || (2*i+2 < n && a[i] > a[2*i+2]));
  assert exists k :: 0 <= k < n/2 && (a[k] > a[2*k + 1] || (2*k + 2 < n && a[k] > a[2*k + 2]))
    by { witness i; }
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
  var n := a.Length;
  var i := 0;
  while i < n / 2
    invariant 0 <= i <= n / 2
    invariant forall j :: 0 <= j < i ==> a[j] <= a[2*j + 1] && (2*j + 2 == n || a[j] <= a[2*j + 2])
  {
    var left := 2*i + 1;
    var right := 2*i + 2;
    if left >= n {
      break;
    }
    if a[i] > a[left] || (right < n && a[i] > a[right]) {
      // Help the verifier witness the existence required by the postcondition
      assert 0 <= i < n/2;
      assert 2*i+1 < n;
      assert a[i] > a[2*i+1] || (2*i+2 < n && a[i] > a[2*i+2]);
      ViolationImpliesExists(a, i, n);
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>

