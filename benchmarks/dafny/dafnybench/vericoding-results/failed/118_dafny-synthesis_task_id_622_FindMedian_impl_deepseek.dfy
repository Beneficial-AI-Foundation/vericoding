

// <vc-helpers>
lemma ArrayPropertyLemma(a: array<int>, b: array<int>)
    requires a.Length == b.Length
    requires a.Length > 0
    requires forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i + 1]
    requires forall i :: 0 <= i < b.Length - 1 ==> b[i] <= b[i + 1]
    requires a[0] <= b[b.Length - 1]
    ensures forall i :: 0 <= i < a.Length ==> a[i] <= b[i]
{
    var j := 0;
    while j < a.Length
        invariant 0 <= j <= a.Length
        invariant forall i :: 0 <= i < j ==> a[i] <= b[i]
    {
        if j > 0 {
            assert a[j] <= a[a.Length - 1] by {
                if j < a.Length - 1 {
                    var k := j;
                    while k < a.Length - 1
                        invariant j <= k <= a.Length - 1
                        invariant a[j] <= a[k]
                    {
                        assert a[k] <= a[k + 1];
                        k := k + 1;
                    }
                }
            }
            assert a[a.Length - 1] <= b[b.Length - 1] by {
                assert a[0] <= b[b.Length - 1];
                var k := 0;
                while k < a.Length - 1
                    invariant 0 <= k <= a.Length - 1
                    invariant a[k] <= b[b.Length - 1]
                {
                    assert a[k] <= a[k + 1];
                    assert a[k] <= b[b.Length - 1];
                    k := k + 1;
                }
            }
            assert b[b.Length - 1] >= b[j] by {
                var k := j;
                while k < b.Length - 1
                    invariant j <= k <= b.Length - 1
                    invariant b[j] <= b[k]
                {
                    assert b[k] <= b[k + 1];
                    k := k + 1;
                }
            }
            assert a[j] <= b[j] by {
                assert a[j] <= a[a.Length - 1];
                assert a[a.Length - 1] <= b[b.Length - 1];
                assert b[b.Length - 1] >= b[j];
            }
        } else {
            assert a[0] <= b[0] by {
                assert a[0] <= b[b.Length - 1];
                var k := 0;
                while k < b.Length - 1
                    invariant 0 <= k <= b.Length - 1
                    invariant a[0] <= b[k]
                {
                    assert b[k] <= b[k + 1];
                    k := k + 1;
                }
            }
        }
        j := j + 1;
    }
}
// </vc-helpers>

// <vc-spec>
method FindMedian(a: array<int>, b: array<int>) returns (median: int)
    requires a != null && b != null
    requires a.Length == b.Length
    requires a.Length > 0
    requires forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i + 1]
    requires forall i :: 0 <= i < b.Length - 1 ==> b[i] <= b[i + 1]
    ensures median == if (a.Length % 2 == 0) then (a[a.Length / 2 - 1] + b[0]) / 2 else a[a.Length / 2]
// </vc-spec>
// <vc-code>
{
  ArrayPropertyLemma(a, b);
  if a.Length % 2 == 0 {
    median := (a[a.Length / 2 - 1] + b[b.Length / 2]) / 2;
  } else {
    median := a[a.Length / 2];
  }
}
// </vc-code>

