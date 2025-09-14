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
function prefixCount(a: string, n: int, ch: char): int
  requires 0 <= n <= |a|
{
  if n == 0 then 0 else prefixCount(a, n-1, ch) + (if a[n-1] == ch then 1 else 0)
}

lemma MultisetPrefixCount(a: string, n: int, ch: char)
  requires 0 <= n <= |a|
  ensures multiset(a[..n])[ch] == prefixCount(a, n, ch)
{
  if n == 0 {
    // multiset(a[..0])[ch] == 0 and prefixCount(a,0,ch) == 0
  } else {
    MultisetPrefixCount(a, n-1, ch);
    // counts for concatenation: a[..n] == a[..n-1] + a[n-1..n]
    assert multiset(a[..n])[ch] == multiset(a[..n-1])[ch] + multiset(a[n-1..n])[ch];
    // single-character slice has count 1 for its character, 0 otherwise
    assert multiset(a[n-1..n])[ch] == (if a[n-1] == ch then 1 else 0);
    // combine with inductive hypothesis
    assert multiset(a[..n])[ch] == prefixCount(a, n-1, ch) + (if a[n-1] == ch then 1 else 0);
    // which is exactly prefixCount(a,n,ch)
    assert multiset(a[..n])[ch] == prefixCount(a, n, ch);
  }
}
// </vc-helpers>

// <vc-spec>
method BadSort(a: string) returns (b: string)
requires forall k :: 0 <= k < |a| ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd';
ensures sortedbad(b);
ensures multiset(a[..]) == multiset(b[..]);
ensures |a| == |b|;
// </vc-spec>
// <vc-code>
{
  var nb := 0;
  var na := 0;
  var nd := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant prefixCount(a, i, 'b') == nb
    invariant prefixCount(a, i, 'a') == na
    invariant prefixCount(a, i, 'd') == nd
  {
    var old_nb := nb;
    var old_na := na;
    var old_nd := nd;
    var c := a[i];
    i := i + 1;
    if c == 'b' {
      nb := old_nb + 1;
    } else if c == 'a' {
      na := old_na + 1;
    } else {
      // By the precondition, the character must be 'd'
      assert c == 'd';
      nd := old_nd + 1;
    }

    // Use the definition of prefixCount to reestablish invariants
    assert prefixCount(a, i, 'b') == prefixCount(a, i-1, 'b') + (if c == 'b' then 1 else 0);
    assert prefixCount(a, i-1, 'b') == old_nb;
    assert nb == old_nb + (if c == 'b' then 1 else 0);
    assert prefixCount(a, i, 'b') == nb;

    assert prefixCount(a, i, 'a') == prefixCount(a, i-1, 'a') + (if c == 'a' then 1 else 0);
    assert prefixCount(a, i-1, 'a') == old_na;
    assert na == old_na + (if c == 'a' then 1 else 0);
    assert prefixCount(a, i, 'a') == na;

    assert prefixCount(a, i, 'd') == prefixCount(a, i-1, 'd') + (if c == 'd' then 1 else 0);
    assert prefixCount(a, i-1, 'd') == old_nd;
    assert nd == old_nd + (if c == 'd' then 1 else 0);
    assert prefixCount(a, i, 'd') == nd;
  }

  var res := "";
  var j := 0;
  // build b's
  while j < nb
    invariant 0 <= j <= nb
    invariant |res| == j
    invariant forall k :: 0 <= k < |res| ==> res[k] == 'b'
  {
    res := res + "b";
    j := j + 1;
  }

  var j2 := 0;
  // build a's
  while j2 < na
    invariant 0 <= j2 <= na
    invariant |res| == nb + j2
    invariant forall k :: 0 <= k < nb ==> res[k] == 'b'
    invariant forall k :: nb <= k < |res| ==> res[k] == 'a'
  {
    res := res + "a";
    j2 := j2 + 1;
  }

  var j3 := 0;
  // build d's
  while j3 < nd
    invariant 0 <= j3 <= nd
    invariant |res| == nb + na + j3
    invariant forall k :: 0 <= k < nb ==> res[k] == 'b'
    invariant forall k :: nb <= k < nb + na ==> res[k] == 'a'
    invariant forall k :: nb + na <= k < |res| ==> res[k] == 'd'
  {
    res := res + "d";
    j3 := j3 + 1;
  }

  // prove multiset equality via prefixCount connection
  MultisetPrefixCount(a, |a|, 'b');
  MultisetPrefixCount(a, |a|, 'a');
  MultisetPrefixCount(a, |a|, 'd');
  MultisetPrefixCount(res, |res|, 'b');
  MultisetPrefixCount(res, |res|, 'a');
  MultisetPrefixCount(res, |res|, 'd');

  assert multiset(a[..])[ 'b'] == prefixCount(a, |a|, 'b');
  assert multiset(a[..])[ 'a'] == prefixCount(a, |a|, 'a');
  assert multiset(a[..])[ 'd'] == prefixCount(a, |a|, 'd');

  assert multiset(res[..])[ 'b'] == prefixCount(res, |res|, 'b');
  assert multiset(res[..])[ 'a'] == prefixCount(res, |res|, 'a');
  assert multiset(res[..])[ 'd'] == prefixCount(res, |res|, 'd');

  assert prefixCount(a, |a|, 'b') == nb;
  assert prefixCount(a, |a|, 'a') == na;
  assert prefixCount(a, |a|, 'd') == nd;
  assert prefixCount(res, |res|, 'b') == nb;
  assert prefixCount(res, |res|, 'a') == na;
  assert prefixCount(res, |res|, 'd') == nd;

  // all characters in res are among 'b','a','d'
  assert forall k :: 0 <= k < |res| ==> res[k] == 'b' || res[k] == 'a' || res[k] == 'd';

  // conclude multisets equal
  assert forall ch ::
    if ch == 'b' then multiset(a[..])[ch] == multiset(res[..])[ch]
    else if ch == 'a' then multiset(a[..])[ch] == multiset(res[..])[ch]
    else if ch == 'd' then multiset(a[..])[ch] == multiset(res[..])[ch]
    else multiset(a[..])[ch] == 0 && multiset(res[..])[ch] == 0;
  assert multiset(a[..]) == multiset(res[..]);

  // prove sortedbad(res)
  // b's are in indices [0, nb), a's in [nb, nb+na), d's in [nb+na, end)
  assert forall p,q ::
    0 <= p < |res| && 0 <= q < |res| &&
    res[p] == 'b' && (res[q] == 'a' || res[q] == 'd') ==> p < q;
  assert forall p,q ::
    0 <= p < |res| && 0 <= q < |res| && res[p] == 'a' && res[q] == 'b' ==> p > q;
  assert forall p,q ::
    0 <= p < |res| && 0 <= q < |res| && res[p] == 'a' && res[q] == 'd' ==> p < q;
  assert forall p,q ::
    0 <= p < |res| && 0 <= q < |res| && res[p] == 'd' && (res[q] == 'a' || res[q] == 'b') ==> p > q;

  b := res;
}
// </vc-code>

