// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/G4sc3

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://rise4fun.com/Dafny/nujsu

// Insertion sort með hjálp helmingunarleitar.

// <vc-helpers>
lemma sorted_leq(s: seq<int>, i: int, j: int)
  requires 0 <= i <= j < |s|
  requires forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
  ensures s[i] <= s[j]
{
  if i < j {
    assert 0 <= i < j < |s|;
    assert s[i] <= s[j];
  }
}

lemma prefix_members_bounded(s: seq<int>, k: int, x: int)
  requires 0 <= k <= |s|
  requires forall i | 0 <= i < k :: s[i] <= x
  ensures forall z | z in s[..k] :: z <= x
{
  forall z | z in s[..k]
    ensures z <= x
  {
    var j :| 0 <= j < |s[..k]| && s[..k][j] == z;
    assert |s[..k]| == k;
    assert 0 <= j < k;
    assert s[..k][j] == s[j];
    assert s[j] <= x;
  }
}

lemma suffix_members_bounded(s: seq<int>, k: int, x: int)
  requires 0 <= k <= |s|
  requires forall i | k <= i < |s| :: s[i] >= x
  ensures forall z | z in s[k..] :: z >= x
{
  forall z | z in s[k..]
    ensures z >= x
  {
    var j :| 0 <= j < |s[k..]| && s[k..][j] == z;
    assert |s[k..]| == |s| - k;
    assert 0 <= j < |s| - k;
    assert k <= k + j < |s|;
    assert s[k..][j] == s[k + j];
    assert s[k + j] >= x;
  }
}
// </vc-helpers>

// <vc-spec>
method Search( s: seq<int>, x: int ) returns ( k: int )
    // Ekki má breyta forskilyrðum eða eftirskilyrðum fallsins
    requires forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
    ensures 0 <= k <= |s|;
    ensures forall i | 0 <= i < k :: s[i] <= x;
    ensures forall i | k <= i < |s| :: s[i] >= x;
    ensures forall z | z in s[..k] :: z <= x;
    ensures forall z | z in s[k..] :: z >= x;
    ensures s == s[..k]+s[k..];
// </vc-spec>
// <vc-code>
{
  var lo := 0;
  var hi := |s|;
  while lo < hi
    invariant 0 <= lo <= hi <= |s|
    invariant forall i | 0 <= i < lo :: s[i] <= x
    invariant forall i | hi <= i < |s| :: s[i] >= x
    decreases hi - lo
  {
    var mid := lo + (hi - lo) / 2;
    assert lo <= mid < hi;
    if s[mid] < x {
      assert forall i | 0 <= i < mid + 1 :: s[i] <= x by {
        forall i | 0 <= i < mid + 1
          ensures s[i] <= x
        {
          if i < mid {
            if i < lo {
              // from invariant
            } else {
              assert 0 <= i < mid < |s|;
              assert s[i] <= s[mid];
              assert s[mid] <= x;
            }
          } else {
            assert i == mid;
            assert s[i] == s[mid];
          }
        }
      };
      lo := mid + 1;
    } else {
      assert forall i | mid <= i < |s| :: s[i] >= x by {
        forall i | mid <= i < |s|
          ensures s[i] >= x
        {
          if i == mid {
            assert x <= s[i];
          } else {
            assert mid < i < |s|;
            assert 0 <= mid < i < |s|;
            assert s[mid] <= s[i];
            assert x <= s[mid];
            assert x <= s[i];
          }
        }
      };
      hi := mid;
    }
  }
  k := lo;
  assert lo == hi;
  assert 0 <= k <= |s|;
  prefix_members_bounded(s, k, x);
  suffix_members_bounded(s, k, x);
  assert s == s[..k] + s[k..];
}
// </vc-code>

