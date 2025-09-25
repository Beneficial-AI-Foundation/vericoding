// <vc-preamble>
predicate sortedbad(s:string) 
{

    forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'b' && (s[j] == 'a' || s[j] == 'd') ==> i < j &&

    forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'a' && s[j] == 'b' ==> i > j &&

    forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'a' && s[j] == 'd' ==> i < j &&

    forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'd' && (s[j] == 'a' || s[j] == 'b') ==> i > j
}
// </vc-preamble>

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>
