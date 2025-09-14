

// <vc-helpers>
lemma FindZero_Property(a: array<int>, i: int, k: int)
  requires 0 <= i <= k < a.Length
  requires forall x :: i <= x < k ==> 0 <= a[x]
  requires forall x :: 0 < x < a.Length ==> a[x-1]-1 <= a[x]
  ensures i == k || a[i] <= a[k] + (k - i)
{
  if i < k {
    var j := i;
    while j < k
      invariant i <= j <= k
      invariant a[i] <= a[j] + (j - i)
      decreases k - j
    {
      if j + 1 < a.Length {
        calc {
          a[j];
          { // a[j]-1 <= a[j+1]  ==> a[j] <= a[j+1] + 1
            assert a[j]-1 <= a[j+1];
          }
          a[j+1] + 1;
        }
        assert a[j] <= a[j+1] + 1;
        assert a[j] <= a[j+1] + ((j+1) - j); //
        assert a[i] <= a[j] + (j - i); // invariant
        assert a[i] <= (a[j+1] + 1) + (j - i);
        assert a[i] <= a[j+1] + ( (j+1) - i ) ;
      }
      j := j + 1;
    }
  }
}

lemma FindZero_Property2(a: array<int>, i: int, k: int)
  requires 0 <= i <= k < a.Length
  requires forall x :: 0 < x < a.Length ==> a[x-1]-1 <= a[x]
  ensures a[k] <= a[i] + (k - i)
{
  if i < k
  {
    var j := k;
    while j > i
      invariant i <= j <= k
      invariant a[k] <= a[j] + (k - j)
      decreases j - i
    {
      if j - 1 >= 0 {
        calc {
          a[j-1];
          { // a[j-1]-1 <= a[j] ==> a[j-1] <= a[j] + 1
            assert a[j-1]-1 <= a[j];
          }
          a[j] + 1;
        }
        assert a[j-1] <= a[j] + 1;
        assert a[k] <= a[j] + (k - j);
        assert a[k] <= (a[j-1] + 1) + (k - j);
        assert a[k] <= a[j-1] + (k - (j-1));
      }
      j := j - 1;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method FindZero(a: array<int>) returns (index: int)
   requires a != null
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
   ensures index < 0  ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
   ensures 0 <= index ==> index < a.Length && a[index] == 0
// </vc-spec>
// <vc-code>
{
    var low := 0;
    var high := a.Length;
    index := -1; // Default to not found

    if a.Length == 0 {
      return;
    }

    while low < high
        invariant 0 <= low <= high <= a.Length
        invariant (exists k_root :: 0 <= k_root < a.Length && a[k_root] == 0) ==> (exists k_target :: low <= k_target < high && a[k_target] == 0) || (forall k_left :: 0 <= k_left < low ==> a[k_left] > 0) || (forall k_right :: high <= k_right < a.Length ==> a[k_right] > 0)
        invariant (forall k :: 0 <= k < low ==> a[k] > 0)
        invariant (forall k :: high <= k < a.Length ==> a[k] > 0)
        invariant (forall k :: low <= k < high ==> a[k] >= 0)
        decreases high - low
    {
        var mid := low + (high - low) / 2;
        assert low <= mid < high;

        if a[mid] == 0 {
            // FindZero_Property and FindZero_Property2 require a non-null array argument.
            // We know 'a' is non-null from pre-conditions.
            // If a[mid] is 0, any 0 must be in the range [low, mid].
            // We use FindZero_Property2 to establish that if a[mid]=0, then all elements
            // from low to mid are positive or a zero is present in [low, mid].
            // Specifically, a[mid] <= a[low] + (mid - low) implies a[low] >= a[mid] - (mid - low).
            // Since a[mid] is 0, a[low] >= -(mid - low). We already know a[low] >= 0.
            if low <= mid {
              FindZero_Property2(a, low, mid);
              // a[mid] <= a[low] + (mid - low) is implied by FindZero_Property2
              assert a[mid] <= a[low] + (mid - low);
            }
            high := mid;
        } else if mid + 1 < a.Length && a[mid] > a[mid+1] {
            // This condition is not possible given the requirement: forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
            // If a[mid] > a[mid+1], then a[mid] >= a[mid+1] + 1.
            // But a[mid]-1 <= a[mid+1] implies a[mid] <= a[mid+1] + 1.
            // So, a[mid] must be exactly a[mid+1] + 1.
            // This branch implies that if a zero exists, it must be in [mid+1, high).
            low := mid + 1;
        } else {
            // a[mid] > 0 AND (mid + 1 >= a.Length OR a[mid] <= a[mid+1])
            // In this case, if zero exists, it must be in [low, mid].
            // We use FindZero_Property to establish that if array elements are
            // non-negative in [low, mid], a[low] <= a[mid] + (mid - low) holds.
            FindZero_Property(a, low, mid);
            // a[low] <= a[mid] + (mid - low) is implied by FindZero_Property
            assert a[low] <= a[mid] + (mid - low);
            high := mid;
        }
    }

    if low < a.Length && a[low] == 0 {
        index := low;
    } else {
        index := -1;
    }
}
// </vc-code>

