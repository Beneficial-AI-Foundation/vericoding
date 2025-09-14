// method verifies

// <vc-helpers>
lemma MultisetSwapSingle<T>(left: seq<T>, mid: seq<T>, right: seq<T>, x: T, y: T)
  ensures multiset(left + [x] + mid + [y] + right) == multiset(left + [y] + mid + [x] + right)
{
  calc {
    multiset(left + [x] + mid + [y] + right);
    == { }
      multiset(left) + multiset([x]) + multiset(mid) + multiset([y]) + multiset(right);
    == { }
      multiset(left) + multiset([y]) + multiset(mid) + multiset([x]) + multiset(right);
    == { }
      multiset(left + [y] + mid + [x] + right);
  }
}

lemma PartitionSeq<T>(a: seq<T>, i: nat, j: nat)
  requires i < j && j < |a|
  ensures a == a[..i] + [a[i]] + a[i+1..j] + [a[j]] + a[j+1..]
{
  calc {
    a;
    == { }
      a[..i] + a[i..];
    == { }
      a[..i] + ([a[i]] + a[i+1..]);
    == { }
      a[..i] + [a[i]] + a[i+1..];
    == { }
      a[..i] + [a[i]] + (a[i+1..j] + a[j..]);
    == { }
      a[..i] + [a[i]] + a[i+1..j] + a[j..];
    == { }
      a[..i] + [a[i]] + a[i+1..j] + ([a[j]] + a[j+1..]);
    == { }
      a[..i] + [a[i]] + a[i+1..j] + [a[j]] + a[j+1..];
  }
}

lemma SwapPreservesOthers<T>(a: seq<T>, i:nat, j:nat, left: seq<T>, mid: seq<T>, right: seq<T>, seqt: seq<T>)
  requires i < j && j < |a|
  requires left == a[..i]
  requires mid == a[i+1..j]
  requires right == a[j+1..]
  requires seqt == left + [a[j]] + mid + [a[i]] + right
  ensures forall k:nat :: k != i && k != j && k < |a| ==> seqt[k] == a[k]
{
  assert forall k:nat | k != i && k != j && k < |a| {
    if k < i {
      calc {
        seqt[k];
        == { }
          (left + [a[j]] + mid + [a[i]] + right)[k];
        == { }
          left[k];
        == { }
          a[..i][k];
        == { }
          a[k];
      }
    } else if i < k && k < j {
      calc {
        seqt[k];
        == { }
          (left + [a[j]] + mid + [a[i]] + right)[k];
        == { }
          mid[k-(i+1)];
        == { }
          a[i+1..j][k-(i+1)];
        == { }
          a[k];
      }
    } else {
      calc {
        seqt[k];
        == { }
          (left + [a[j]] + mid + [a[i]] + right)[k];
        == { }
          right[k-(j+1)];
        == { }
          a[j+1..][k-(j+1)];
        == { }
          a[k];
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method StringSwap(s: string, i:nat, j:nat) returns (t: string)
requires i >= 0 && j >= 0 && |s| >= 0;
requires |s| > 0 ==> i < |s| && j < |s|;
ensures multiset(s[..]) == multiset(t[..]);
ensures |s| == |t|;
ensures |s| > 0 ==> forall k:nat :: k != i && k != j && k < |s| ==> t[k] == s[k]
ensures |s| > 0 ==> t[i] == s[j] && t[j] == s[i];
ensures |s| == 0 ==> t == s;
// </vc-spec>
// <vc-code>
{
  var a := s[..];
  if |s| == 0 {
    t := s;
    return;
  }
  var i0 := i;
  var j0 := j;
  if i0 > j0 {
    var tmp := i0;
    i0 := j0;
    j0 := tmp;
  }
  if i0 == j0 {
    t := s;
    return;
  }
  var left := a[..i0];
  var mid := a[i0+1..j0];
  var right := a[j0+1..];
  var seqt := left + [a[j0]] + mid + [a[i0]] + right;
  PartitionSeq(a, i0, j0);
  assert a == left + [a[i0]] + mid + [a[j0]] + right;
  assert seqt == left + [a[j0]] + mid + [a[i0]] + right;
  MultisetSwapSingle(left, mid, right, a[i0], a[j0]);
  assert multiset(a) == multiset(seqt);
  SwapPreservesOthers(a, i0, j0, left, mid, right, seqt);
  assert forall k:nat :: k != i0 && k != j0 && k < |a| ==> seqt[k] == a[k];
  t := seqt;
}
// </vc-code>

// string == seq<Char>
//give se2011 ass2 ex1.dfy