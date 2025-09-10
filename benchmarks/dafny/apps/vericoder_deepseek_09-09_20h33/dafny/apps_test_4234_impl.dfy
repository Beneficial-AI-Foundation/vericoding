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

lemma GoodStringPreserved(s: string, i: int, j: int, buf: array<char>)
  requires 0 <= i <= j <= |s|
  requires IsGoodString(buf[0..i])
  requires forall k :: 0 <= k < i ==> buf[k] == s[k]
  requires forall k :: i <= k < j ==> (k % 2 == 0 ==> k+1 < |s| && s[k] != s[k+1]) && (k % 2 == 1 ==> buf[k-1] != s[k])
  ensures IsGoodString(buf[0..i])
{
}

lemma EvenLengthGoodString(s: string)
  requires IsGoodString(s)
  ensures |s| % 2 == 0
{
}

lemma EvenInvariantMaintained(i: int, step: int)
  requires i % 2 == 0
  ensures (i + step) % 2 == step % 2
{
}

lemma GoodStringExtend(s: string, buf: array<char>, i: int, j: int)
  requires 0 <= i <= j < |s|
  requires IsGoodString(buf[0..i])
  requires i % 2 == 0
  requires buf[i] == s[j]
  requires i > 0 ==> buf[i-1] != s[j]
  ensures IsGoodString(buf[0..i+1])
{
}

lemma BufferIndexSafety(buf: array<char>, i: int)
  requires 0 <= i <= buf.Length
  ensures 0 <= i < buf.Length ==> buf[i] is char
{
}
// </vc-helpers>
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
    invariant forall k :: i <= k < j ==> (k % 2 == 0 ==> k+1 < n && s[k] != s[k+1]) && (k % 2 == 1 ==> k-1 >= 0 && buf[k-1] != s[k])
  {
    if i % 2 == 0 || (i > 0 && buf[i-1] != s[j]) {
      buf[i] := s[j];
      i := i + 1;
    } else {
      deletedCount := deletedCount + 1;
    }
    j := j + 1;
  }
  
  result := buf[0..i];
}
// </vc-code>

