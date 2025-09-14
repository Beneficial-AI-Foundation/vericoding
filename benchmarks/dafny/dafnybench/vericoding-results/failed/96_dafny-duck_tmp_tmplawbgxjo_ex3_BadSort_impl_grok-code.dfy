// program verifies

predicate sortedbad(s: string)
{
  // no b's after non-b's
  forall i, j :: 0 <= i <= j < |s| && s[i] == 'b' && s[j] != 'b' ==> i < j &&
  // only non-d's before d's
  forall i, j :: 0 <= i <= j < |s| && s[i] != 'd' && s[j] == 'd' ==> i < j
}

// <vc-helpers>
predicate sortedbad(s: string)
{
  (forall i, j :: 0 <= i <= j < |s| && s[i] == 'b' && s[j] != 'b' ==> i < j) &&
  (forall i, j :: 0 <= i <= j < |s| && s[i] != 'd' && s[j] == 'd' ==> i < j)
}
// </vc-helpers>

// <vc-spec>
method BadSort(a: string) returns (b: string)
requires forall i :: 0<=i<|a| ==> a[i] in {'b', 'a', 'd'}
ensures sortedbad(b)
ensures multiset(b[..]) == multiset(a[..])
// </vc-spec>
// <vc-code>
{
  var numA := 0;
  var numB := 0;
  var numD := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant multiset(a[..i])['a'] == numA && multiset(a[..i])['b'] == numB && multiset(a[..i])['d'] == numD
  {
    match a[i] {
      case 'a' => numA := numA + 1;
      case 'b' => numB := numB + 1;
      case 'd' => numD := numD + 1;
    }
    i := i + 1;
  }

  i := 0;
  b := [];
  while i < numB
    invariant 0 <= i <= numB
    invariant |b| == i
    invariant forall k :: 0 <= k < |b| ==> b[k] == 'b'
  {
    b := b + ['b'];
    i := i + 1;
  }
  i := 0;
  while i < numA
    invariant 0 <= i <= numA
    invariant |b| == numB + i
    invariant forall k :: 0 <= k < numB ==> b[k] == 'b'
    invariant forall k :: numB <= k < |b| ==> b[k] == 'a'
  {
    b := b + ['a'];
    i := i + 1;
  }
  i := 0;
  while i < numD
    invariant 0 <= i <= numD
    invariant |b| == numB + numA + i
    invariant forall k :: 0 <= k < numB ==> b[k] == 'b'
    invariant forall k :: numB <= k < numB + numA ==> b[k] == 'a'
    invariant forall k :: numB + numA <= k < |b| ==> b[k] == 'd'
  {
    b := b + ['d'];
    i := i + 1;
  }
}
// </vc-code>

