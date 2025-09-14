// http://verifythus.cost-ic0701.org/common-example/arraymax-in-dafny

// <vc-helpers>
lemma max_index_property(a: array<int>, i: int, j: int)
  requires a != null
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  ensures a[i] >= a[j] || a[j] >= a[i]
{
}

lemma max_transitive_property(a: array<int>, x: int, y: int, z: int)
  requires a != null
  requires 0 <= x < a.Length && 0 <= y < a.Length && 0 <= z < a.Length
  ensures a[x] >= a[y] && a[y] >= a[z] ==> a[x] >= a[z]
{
}

lemma max_int_property(a: array<int>, index: int, maxVal: int)
  requires a != null
  requires 0 <= index <= a.Length
  requires forall k :: 0 <= k < index ==> maxVal >= a[k]
  requires exists k :: 0 <= k < index && maxVal == a[k]
  requires index < a.Length
  ensures forall k :: 0 <= k <= index ==> maxVal >= a[k] || a[index] >= a[k]
  ensures exists k :: 0 <= k <= index && (if a[index] > maxVal then a[index] else maxVal) == a[k]
{
  var newMax := if a[index] > maxVal then a[index] else maxVal;
  if a[index] > maxVal {
    assert forall k :: 0 <= k <= index ==> newMax >= a[k] by {
      forall k | 0 <= k <= index {
        if k < index {
          assert maxVal >= a[k];
          assert newMax > maxVal ==> newMax > a[k];
        } else if k == index {
          assert newMax == a[index];
        }
      }
    }
    assert exists k :: 0 <= k <= index && newMax == a[k] by {
      assert newMax == a[index];
    }
  } else {
    assert forall k :: 0 <= k <= index ==> newMax >= a[k] by {
      forall k | 0 <= k <= index {
        if k < index {
          assert maxVal >= a[k];
        } else if k == index {
          assert newMax == maxVal;
          assert maxVal >= a[index];
        }
      }
    }
    assert exists k :: 0 <= k <= index && newMax == a[k] by {
      var witness :| 0 <= witness < index && maxVal == a[witness];
      assert newMax == a[witness];
    }
  }
}
// </vc-helpers>

// <vc-spec>
method max(a:array<int>) returns(max:int)
    requires a != null;
    ensures forall j :: j >= 0 && j < a.Length ==> max >= a[j]; //max is larger then anything in the array
    ensures a.Length > 0 ==> exists j :: j >= 0 && j < a.Length && max == a[j]; //max is an element in the array
// </vc-spec>
// <vc-code>
{
  if a.Length == 0 {
    max := 0;
  } else {
    max := a[0];
    var index := 1;
    
    while index < a.Length
      invariant 1 <= index <= a.Length
      invariant forall k :: 0 <= k < index ==> max >= a[k]
      invariant exists k :: 0 <= k < index && max == a[k]
    {
      if a[index] > max {
        max := a[index];
      }
      index := index + 1;
      max_int_property(a, index - 1, old(max));
    }
  }
}
// </vc-code>

