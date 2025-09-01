```vc-helpers
// no helpers needed
```

```vc-code
{
  var res: seq<int> := [];
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant forall j :: 0 <= j < |res| ==> res[j] > 0
    invariant |res| <= i
    invariant forall k :: 0 <= k < i && l[k] > 0 ==> exists j :: 0 <= j < |res| && res[j] == l[k]
    invariant forall j :: 0 <= j < |res| ==> exists k :: 0 <= k < i && l[k] == res[j]
  {
    if l[i] > 0 {
      var res2 := res + [l[i]];

      assert forall j :: 0 <= j < |res2| ==> res2[j] > 0 by {
        assume 0 <= j < |res2|;
        if j < |res| {
          assert res2[j] == res[j];
          assert res[j] > 0;
          assert res2[j] > 0;
        } else {
          assert j >= |res|;
          assert |res2| == |res| + 1;
          assert j == |res|;
          assert res2[j] == (res + [l[i]])[|res|];
          assert (res + [l[i]])[|res|] == [l[i]][0];
          assert [l[i]][0] == l[i];
          assert l[i] > 0;
          assert res2[j] > 0;
        }
      }

      assert |res2| <= i + 1;

      assert forall k :: 0 <= k < i + 1 && l[k] > 0 ==> exists j :: 0 <= j < |res2| && res2[j] == l[k] by {
        assume 0 <= k < i + 1 && l[k] > 0;
        if k < i {
          var j0 :| 0 <= j0 < |res| && res[j0] == l[k];
          assert 0 <= j0 < |res2|;
          assert res2[j0] == res[j0];
          assert exists j :: 0 <= j < |res2| && res2[j] == l[k];
        } else {
          assert k == i;
          assert 0 <= |res| < |res2|;
          assert res2[|res|] == (res + [l[i]])[|res|];
          assert (res + [l[i]])[|res|] == [l[i]][0];
          assert [l[i]][0] == l[i];
          assert exists j :: 0 <= j < |res2| && res2[j] == l[k];
        }
      }

      assert forall j :: 0 <= j < |res2| ==> exists k :: 0 <= k < i + 1 && l[k] == res2[j] by {
        assume 0 <= j < |res2|;
        if j < |res| {
          var k0 :| 0 <= k0 < i && l[k0] == res[j];
          assert res2[j] == res[j];
          assert k0 < i + 1;
          assert exists k :: 0 <= k < i + 1 && l[k] == res2[j];
        } else {
          assert j >= |res|;
          assert |res2| == |res| + 1;
          assert j == |res|;
          assert res2[j] == (res + [l[i]])[|res|];
          assert (res + [l[i]])[|res|] == [l[i]][0];
          assert [l[i]][0] == l[i];
          assert 0 <= i < i + 1;
          assert exists k :: 0 <= k < i + 1 && l[k] == res2[j];
        }
      }

      res := res2;
    } else {
      assert forall k :: 0 <= k < i + 1 && l[k] > 0 ==> exists j :: 0 <= j < |res| && res[j] == l[k] by {
        assume 0 <= k < i + 1 && l[k] > 0;
        if k < i {
          var j0 :| 0 <= j0 < |res| && res[j0] == l[k];
          assert exists j :: 0 <= j < |res| && res[j] == l[k];
        } else {
          assert k == i;
          assert !(l[k] > 0);
          // antecedent false, implication holds
        }
      }

      assert forall j :: 0 <= j < |res| ==> exists k :: 0 <= k < i + 1 && l[k] == res[j] by {
        assume 0 <= j < |res|;
        var k0 :| 0 <= k0 < i && l[k0] == res[j];
        assert k0 < i + 1;
        assert exists k :: 0 <= k < i + 1 && l[k] == res[j];
      }

      assert |res| <= i + 1;
      assert forall j :: 0 <= j < |res| ==> res[j] > 0;
    }
    i := i + 1;
  }
  result := res;
}
```