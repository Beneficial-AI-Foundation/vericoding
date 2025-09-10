predicate ValidInput(n: int, s: string)
{
    n == |s| && n >= 0
}

predicate IsGoodString(s: string)
{
    |s| % 2 == 0 && forall i :: 0 <= i < |s|/2 ==> s[2*i] != s[2*i+1]
}

// <vc-helpers>
lemma EvenLengthAfterDeletion(s: string, del: int)
  requires del >= 0
  requires |s| - del >= 0
  ensures (|s| - del) % 2 == 0
{
}

lemma GoodStringPreserved(s: string, i: int, j: int)
  requires 0 <= i <= j < |s|
  requires IsGoodString(s[0..i])
  requires forall k :: i <= k < j ==> (k % 2 == 0 ==> s[k] != s[k+1])
  ensures IsGoodString(s[0..j])
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (deletedCount: int, result: string)
    requires ValidInput(n, s)
    ensures deletedCount >= 0
    ensures deletedCount == |s| - |result|
    ensures IsGoodString(result)
    ensures deletedCount + |result| == |s|
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var j := 0;
  var buf := new char[n];
  deletedCount := 0;
  
  while j < n
    invariant 0 <= i <= j <= n
    invariant i % 2 == 0
    invariant deletedCount == j - i
    invariant forall k :: 0 <= k < i ==> buf[k] == s[k]
    invariant IsGoodString(buf[0..i])
    invariant i == 0 || i % 2 == 0
  {
    if i % 2 == 0 || buf[i-1] != s[j] {
      buf[i] := s[j];
      i := i + 1;
    } else {
      deletedCount := deletedCount + 1;
    }
    j := j + 1;
  }
  
  result := buf[0..i];
  deletedCount := deletedCount + (n - j);
  assert |result| == i;
  assert |s| == n;
}
// </vc-code>

