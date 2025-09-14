// verifies
// check that string between indexes low and high-1 are sorted
predicate Sorted(a: string, low:int, high:int)
requires 0 <= low <= high <= |a|
{ 
    forall j, k :: low <= j < k < high ==> a[j] <= a[k] 
}

// <vc-helpers>
lemma Sorted3(s: string)
  requires |s| == 3
  requires s[0] <= s[1] && s[1] <= s[2]
  ensures Sorted(s, 0, |s|)
{
  forall j, k | 0 <= j < k < 3
    ensures s[j] <= s[k]
  {
    if j == 0 {
      if k == 1 {
        assert s[j] <= s[k];
      } else {
        assert k == 2;
        assert s[0] <= s[2];
        assert s[j] <= s[k];
      }
    } else {
      assert j == 1;
      assert k == 2;
      assert s[j] <= s[k];
    }
  }
}
// </vc-helpers>

// <vc-spec>
method String3Sort(a: string) returns (b: string) 
requires |a| == 3;
ensures Sorted(b, 0, |b|);
ensures |a| == |b|;
ensures multiset{b[0], b[1], b[2]} == multiset{a[0], a[1], a[2]};
// </vc-spec>
// <vc-code>
{
  if a[0] <= a[1] {
    if a[1] <= a[2] {
      b := a;
      Sorted3(b);
    } else {
      if a[0] <= a[2] {
        b := a[0..1] + a[2..3] + a[1..2];
        assert |b| == 3;
        assert b[0] <= b[1];
        assert b[1] <= b[2];
        Sorted3(b);
      } else {
        b := a[2..3] + a[0..1] + a[1..2];
        assert |b| == 3;
        assert b[0] <= b[1];
        assert b[1] <= b[2];
        Sorted3(b);
      }
    }
  } else {
    if a[0] <= a[2] {
      b := a[1..2] + a[0..1] + a[2..3];
      assert |b| == 3;
      assert b[0] <= b[1];
      assert b[1] <= b[2];
      Sorted3(b);
    } else {
      if a[1] <= a[2] {
        b := a[1..2] + a[2..3] + a[0..1];
        assert |b| == 3;
        assert b[0] <= b[1];
        assert b[1] <= b[2];
        Sorted3(b);
      } else {
        b := a[2..3] + a[1..2] + a[0..1];
        assert |b| == 3;
        assert b[0] <= b[1];
        assert b[1] <= b[2];
        Sorted3(b);
      }
    }
  }
}
// </vc-code>

