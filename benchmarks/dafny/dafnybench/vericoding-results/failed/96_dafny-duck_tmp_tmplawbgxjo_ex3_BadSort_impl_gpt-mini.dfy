// program verifies

predicate sortedbad(s: string)
{
  // no b's after non-b's
  forall i, j :: 0 <= i <= j < |s| && s[i] == 'b' && s[j] != 'b' ==> i < j &&
  // only non-d's before d's
  forall i, j :: 0 <= i <= j < |s| && s[i] != 'd' && s[j] == 'd' ==> i < j
}

// <vc-helpers>
lemma three_char_multiset_equal(a: string, b: string)
  requires forall i :: 0 <= i < |a| ==> a[i] in {'b', 'a', 'd'}
  requires forall i :: 0 <= i < |b| ==> b[i] in {'b', 'a', 'd'}
  requires multiset(a)['b'] == multiset(b)['b']
  requires multiset(a)['a'] == multiset(b)['a']
  requires multiset(a)['d'] == multiset(b)['d']
  ensures multiset(a) == multiset(b)
{
  // prove equality of multisets by showing equality of counts for every character
  forall c ::
    multiset(a)[c] == multiset(b)[c]
  {
    if c == 'b' || c == 'a' || c == 'd' {
      if c == 'b' {
        assert multiset(a)[c] == multiset(b)[c];
      } else if c == 'a' {
        assert multiset(a)[c] == multiset(b)[c];
      } else {
        assert multiset(a)[c] == multiset(b)[c];
      }
    } else {
      // characters other than 'b','a','d' cannot occur in either string
      assert multiset(a)[c] == 0;
      assert multiset(b)[c] == 0;
    }
  }
  assert multiset(a) == multiset(b);
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
  var nb := 0;
  var na := 0;
  var nd := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant multiset(a[..i])['b'] == nb
    invariant multiset(a[..i])['a'] == na
    invariant multiset(a[..i])['d'] == nd
  {
    var ch := a[i];
    if ch == 'b' {
      nb := nb + 1;
    } else if ch == 'a' {
      na := na + 1;
    } else {
      nd := nd + 1;
    }
    i := i + 1;
  }

  // i == |a| now, so invariants give counts for the whole string
  assert i == |a|;

  b := "";
  var j := 0;
  while j < nb
    invariant 0 <= j <= nb
    invariant multiset(b)['b'] == j
    invariant multiset(b)['a'] == 0
    invariant multiset(b)['d'] == 0
    invariant forall k :: 0 <= k < |b| ==> b[k] in {'b', 'a', 'd'}
  {
    b := b + "b";
    j := j + 1;
  }

  j := 0;
  while j < na
    invariant 0 <= j <= na
    invariant multiset(b)['b'] == nb
    invariant multiset(b)['a'] == j
    invariant multiset(b)['d'] == 0
    invariant forall k :: 0 <= k < |b| ==> b[k] in {'b', 'a', 'd'}
  {
    b := b + "a";
    j := j + 1;
  }

  j := 0;
  while j < nd
    invariant 0 <= j <= nd
    invariant multiset(b)['b'] == nb
    invariant multiset(b)['a'] == na
    invariant multiset(b)['d'] == j
    invariant forall k :: 0 <= k < |b| ==> b[k] in {'b', 'a', 'd'}
  {
    b := b + "d";
    j := j + 1;
  }

  // establish final multiset equality using the helper lemma
  assert multiset(a)['b'] == nb;
  assert multiset(a)['a'] == na;
  assert multiset(a)['d'] == nd;
  assert forall k :: 0 <= k < |b| ==> b[k] in {'b', 'a', 'd'};
  three_char_multiset_equal(a, b);
  // prove sortedbad(b): all b's come before non-b's and non-d's before d's
  // b is constructed as b^nb a^na d^nd, so it satisfies sortedbad
  assert (forall i, j :: 0 <= i <= j < |b| && b[i] == 'b' && b[j] != 'b' ==> i < j);
  assert (forall i, j :: 0 <= i <= j < |b| && b[i] != 'd' && b[j] == 'd' ==> i < j);
}
// </vc-code>

