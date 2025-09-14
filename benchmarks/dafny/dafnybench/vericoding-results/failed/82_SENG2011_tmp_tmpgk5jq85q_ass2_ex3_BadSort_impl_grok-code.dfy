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
lemma LemmaSortedBad(bs: string, aas: string, ds: string)
  requires forall i :: 0 <= i < |bs| ==> bs[i] == 'b'
  requires forall i :: 0 <= i < |aas| ==> aas[i] == 'a'
  requires forall i :: 0 <= i < |ds| ==> ds[i] == 'd'
  ensures sortedbad(bs + aas + ds)
{}
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
  var bs, aas, ds : string := "", "", "";
  for i := 0 to |a| - 1
    invariant 0 <= i <= |a|
    invariant |bs| + |aas| + |ds| == i
    invariant forall k :: 0 <= k < |bs| ==> bs[k] == 'b'
    invariant forall k :: 0 <= k < |aas| ==> aas[k] == 'a'
    invariant forall k :: 0 <= k < |ds| ==> ds[k] == 'd'
    invariant multiset(bs + aas + ds) == multiset(a[0..i])
  {
    var c := a[i];
    assert c == 'b' || c == 'a' || c == 'd';
    if c == 'b' {
      bs := bs + [c];
    } else if c == 'a' {
      aas := aas + [c];
    } else {
      ds := ds + [c];
    }
  }
  b := bs + aas + ds;
  LemmaSortedBad(bs, aas, ds);
}
// </vc-code>

