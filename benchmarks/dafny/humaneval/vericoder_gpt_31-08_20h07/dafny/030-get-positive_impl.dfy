

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method get_positive(l : seq<int>) returns (result : seq<int>)
    // post-conditions-start
    ensures forall i : int :: i >= 0 && i < |result| ==> result[i] > 0
    ensures |result| <= |l|
    ensures forall i1 :: i1 >= 0 && i1 < |l| ==> (l[i1] > 0 ==> exists i2 :: i2 >= 0 && i2 < |result| && result[i2] == l[i1])
    ensures |result| == 0 || (forall i1 : int :: i1 >= 0 && i1 < |result| ==> (exists i2 :: i2 >= 0 && i2 < |l| && l[i2] == result[i1]))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var res: seq<int> := [];
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant forall j :: 0 <= j < |res| ==> res[j] > 0
    invariant |res| <= i
    invariant forall k :: 0 <= k < i && l[k] > 0 ==> exists j :: 0 <= j < |res| && res[j] == l[k]
    invariant forall j :: 0 <= j < |res| ==> exists k :: 0 <= k < i && l[k] == res[j]
    decreases |l| - i
  {
    if l[i] > 0 {
      var res2 := res + [l[i]];
      assert |res2| == |res| + 1;

      assert forall j | 0 <= j < |res2| :: res2[j] > 0 by {
        if j < |res| {
          assert res2[j] == res[j];
          assert res[j] > 0;
        } else {
          assert j == |res|;
          assert res2[j] == [l[i]][0];
          assert [l[i]][0] == l[i];
          assert l[i] > 0;
        }
      }

      assert |res| <= i;
      assert |res| + 1 <= i + 1;
      assert |res2| <= i + 1;

      assert forall k | 0 <= k < i + 1 && l[k] > 0 :: exists j :: 0 <= j < |res2| && res2[j] == l[k] by {
        if k < i {
          var j0 :| 0 <= j0 < |res| && res[j0] == l[k];
          assert 0 <= j0 < |res2|;
          assert res2[j0] == res[j0];
        } else {
          assert k == i;
          assert 0 <= |res| < |res2|;
          assert res2[|res|] == [l[i]][0];
          assert [l[i]][0] == l[i];
        }
      }

      assert forall j | 0 <= j < |res2| :: exists k :: 0 <= k < i + 1 && l[k] == res2[j] by {
        if j < |res| {
          var k0 :| 0 <= k0 < i && l[k0] == res[j];
          assert k0 < i + 1;
          assert res2[j] == res[j];
        } else {
          assert j == |res|;
          assert res2[j] == [l[i]][0];
          assert [l[i]][0] == l[i];
          assert 0 <= i < i + 1;
        }
      }

      res := res2;
    } else {
      assert forall k | 0 <= k < i + 1 && l[k] > 0 :: exists j :: 0 <= j < |res| && res[j] == l[k] by {
        if k < i {
          var j0 :| 0 <= j0 < |res| && res[j0] == l[k];
        } else {
          assert k == i;
          assert !(l[k] > 0);
        }
      }

      assert forall j | 0 <= j < |res| :: exists k :: 0 <= k < i + 1 && l[k] == res[j] by {
        var k0 :| 0 <= k0 < i && l[k0] == res[j];
        assert k0 < i + 1;
      }

      assert |res| <= i + 1;
      assert forall j :: 0 <= j < |res| ==> res[j] > 0;
    }
    i := i + 1;
  }
  result := res;
}
// </vc-code>

