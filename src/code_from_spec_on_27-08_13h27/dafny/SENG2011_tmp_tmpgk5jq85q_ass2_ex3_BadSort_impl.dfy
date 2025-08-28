// verifies
// all bs are before all as which are before all ds

predicate sortedbad(s:string) 
{
    // all b's are before all a's and d's
    forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'b' && (s[j] == 'a' || s[j] == 'd') ==> i < j &&
    // all a's are after all b's
    forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'a' && s[j] == 'b' ==> i > j &&
    // all a's are before all d's
    forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'a' && s[j] == 'd' ==> i < j &&
    // all d's are after a;; b's and a's
    forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'd' && (s[j] == 'a' || s[j] == 'b') ==> i > j
}

// <vc-helpers>
function countChar(s: string, c: char): nat
{
  if |s| == 0 then 0
  else (if s[0] == c then 1 else 0) + countChar(s[1..], c)
}

lemma countCharPreservesMultiset(s: string, c: char)
  ensures countChar(s, c) == multiset(s[..])[c]
{
  if |s| == 0 {
    assert multiset(s[..])[c] == 0;
  } else {
    assert s[..] == [s[0]] + s[1..][..];
    assert multiset(s[..]) == multiset([s[0]]) + multiset(s[1..][..]);
    calc {
      countChar(s, c);
      (if s[0] == c then 1 else 0) + countChar(s[1..], c);
      { countCharPreservesMultiset(s[1..], c); }
      (if s[0] == c then 1 else 0) + multiset(s[1..][..])[c];
      multiset(s[..])[c];
    }
  }
}

lemma sortedStringProperties(s: string, bCount: nat, aCount: nat, dCount: nat)
  requires |s| == bCount + aCount + dCount
  requires forall k :: 0 <= k < |s| ==> s[k] == 'b' || s[k] == 'a' || s[k] == 'd'
  requires countChar(s, 'b') == bCount
  requires countChar(s, 'a') == aCount
  requires countChar(s, 'd') == dCount
  requires sortedbad(s)
  ensures forall i :: 0 <= i < bCount ==> s[i] == 'b'
  ensures forall i :: bCount <= i < bCount + aCount ==> s[i] == 'a'
  ensures forall i :: bCount + aCount <= i < |s| ==> s[i] == 'd'
{
  var n := |s|;
  var ba := bCount + aCount;

  // Prove all 'b's are in positions 0 to bCount-1
  var i := 0;
  while i < bCount
    invariant 0 <= i <= bCount
    invariant forall k :: 0 <= k < i ==> s[k] == 'b'
  {
    if s[i] != 'b' {
      assert s[i] == 'a' || s[i] == 'd';
      assert false;
    }
    i := i + 1;
  }

  // Prove all 'a's are in positions bCount to ba-1
  i := bCount;
  while i < ba
    invariant bCount <= i <= ba
    invariant forall k :: bCount <= k < i ==> s[k] == 'a'
  {
    if s[i] != 'a' {
      assert s[i] == 'd';
      assert false;
    }
    i := i + 1;
  }

  // Prove all 'd's are in positions ba to n-1
  i := ba;
  while i < n
    invariant ba <= i <= n
    invariant forall k :: ba <= k < i ==> s[k] == 'd'
  {
    if s[i] != 'd' {
      assert false;
    }
    i := i + 1;
  }
}

lemma countCharTotal(s: string, c1: char, c2: char, c3: char)
  requires c1 != c2 && c1 != c3 && c2 != c3
  requires forall k :: 0 <= k < |s| ==> s[k] == c1 || s[k] == c2 || s[k] == c3
  ensures countChar(s, c1) + countChar(s, c2) + countChar(s, c3) == |s|
{
  if |s| == 0 {
    assert countChar(s, c1) == 0;
    assert countChar(s, c2) == 0;
    assert countChar(s, c3) == 0;
  } else {
    assert countChar(s, c1) == (if s[0] == c1 then 1 else 0) + countChar(s[1..], c1);
    assert countChar(s, c2) == (if s[0] == c2 then 1 else 0) + countChar(s[1..], c2);
    assert countChar(s, c3) == (if s[0] == c3 then 1 else 0) + countChar(s[1..], c3);
    countCharTotal(s[1..], c1, c2, c3);
    assert s[0] == c1 || s[0] == c2 || s[0] == c3;
    assert (if s[0] == c1 then 1 else 0) + (if s[0] == c2 then 1 else 0) + (if s[0] == c3 then 1 else 0) == 1;
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method BadSort(a: string) returns (b: string)
requires forall k :: 0 <= k < |a| ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd';
ensures sortedbad(b);
ensures multiset(a[..]) == multiset(b[..]);
ensures |a| == |b|;
// </vc-spec>
// </vc-spec>

// <vc-code>
method BadSortImpl(a: string) returns (b: string)
  requires forall k :: 0 <= k < |a| ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd'
  ensures sortedbad(b)
  ensures multiset(a[..]) == multiset(b[..])
  ensures |a| == |b|
{
  var bCount := 0;
  var aCount := 0;
  var dCount := 0;
  var i := 0;

  // Count the number of each character
  while i < |a|
    invariant 0 <= i <= |a|
    invariant bCount == countChar(a[..i], 'b')
    invariant aCount == countChar(a[..i], 'a')
    invariant dCount == countChar(a[..i], 'd')
  {
    if a[i] == 'b' {
      bCount := bCount + 1;
    } else if a[i] == 'a' {
      aCount := aCount + 1;
    } else {
      dCount := dCount + 1;
    }
    i := i + 1;
  }

  countCharPreservesMultiset(a, 'b');
  countCharPreservesMultiset(a, 'a');
  countCharPreservesMultiset(a, 'd');
  countCharTotal(a, 'b', 'a', 'd');
  assert bCount + aCount + dCount == |a|;

  // Construct the sorted string: all 'b's, then all 'a's, then all 'd's
  var res := "";
  i := 0;
  while i < bCount
    invariant 0 <= i <= bCount
    invariant |res| == i
    invariant forall k :: 0 <= k < i ==> res[k] == 'b'
  {
    res := res + "b";
    i := i + 1;
  }
  i := 0;
  while i < aCount
    invariant 0 <= i <= aCount
    invariant |res| == bCount + i
    invariant forall k :: 0 <= k < bCount ==> res[k] == 'b'
    invariant forall k :: bCount <= k < bCount + i ==> res[k] == 'a'
  {
    res := res + "a";
    i := i + 1;
  }
  i := 0;
  while i < dCount
    invariant 0 <= i <= dCount
    invariant |res| == bCount + aCount + i
    invariant forall k :: 0 <= k < bCount ==> res[k] == 'b'
    invariant forall k :: bCount <= k < bCount + aCount ==> res[k] == 'a'
    invariant forall k :: bCount + aCount <= k < bCount + aCount + i ==> res[k] == 'd'
  {
    res := res + "d";
    i := i + 1;
  }

  b := res;
  assert |b| == bCount + aCount + dCount;
  assert |a| == bCount + aCount + dCount;
  assert countChar(b, 'b') == bCount;
  assert countChar(b, 'a') == aCount;
  assert countChar(b, 'd') == dCount;
  countCharPreservesMultiset(b, 'b');
  countCharPreservesMultiset(b, 'a');
  countCharPreservesMultiset(b, 'd');
  assert multiset(b[..])['b'] == bCount;
  assert multiset(b[..])['a'] == aCount;
  assert multiset(b[..])['d'] == dCount;
  assert multiset(a[..])['b'] == bCount;
  assert multiset(a[..])['a'] == aCount;
  assert multiset(a[..])['d'] == dCount;
  assert multiset(b[..]) == multiset(a[..]);
}
// </vc-code>
