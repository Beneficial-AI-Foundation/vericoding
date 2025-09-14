function min(a: int, b: int): int
    ensures min(a, b) <= a && min(a, b) <= b
    ensures min(a, b) == a || min(a, b) == b
{
    if a < b then a else b
}


ghost function minFunction(a: int, b: int): int
    ensures minFunction(a, b) <= a && minFunction(a, b) <= b
    ensures minFunction(a, b) == a || minFunction(a, b) == b
{
    if a < b then a else b
}


// Return a minimum of a.

// <vc-helpers>
type array<T> = array?<T>
// </vc-helpers>

// <vc-spec>
method minArray(a: array<int>) returns (m: int)
    requires a!= null  && a.Length > 0 
    ensures forall k | 0 <= k < a.Length :: m <= a[k]
    ensures exists k | 0 <= k < a.Length :: m == a[k]
// </vc-spec>
// <vc-code>
{
  var m_local := a[0];
  var i := 1;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k | 0 <= k < i :: m_local <= a[k]
    invariant exists k | 0 <= k < i :: m_local == a[k]
  {
    var old_m := m_local;
    if a[i] < old_m {
      m_local := a[i];
    }
    // After the conditional, m_local is either old_m or a[i], in both cases m_local <= a[i].
    if a[i] < old_m {
      assert m_local <= a[i];
    } else {
      // m_local == old_m, and from the invariant old_m <= a[i]
      assert m_local <= a[i];
    }
    // Prove existence of an index in 0..i+1 that equals m_local
    if a[i] < old_m {
      // m_local == a[i], use i as witness for range 0..i+1
      assert m_local == a[i];
      assert 0 <= i && i < i+1;
      assert exists k | 0 <= k < i+1 :: m_local == a[k];
    } else {
      // use the witness guaranteed by the loop invariant for range 0..i
      var kold :| 0 <= kold < i && old_m == a[kold];
      assert m_local == old_m;
      assert 0 <= kold && kold < i+1;
      assert m_local == a[kold];
      assert exists k | 0 <= k < i+1 :: m_local == a[k];
    }
    i := i + 1;
  }
  m := m_local;
}
// </vc-code>

