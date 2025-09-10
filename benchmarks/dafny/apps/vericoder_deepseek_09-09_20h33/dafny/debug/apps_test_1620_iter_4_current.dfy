predicate ValidInput(n: int)
{
  n >= 1
}

predicate ValidOutput(s: string, n: int)
{
  |s| == n &&
  (forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b' || s[i] == 'c') &&
  (forall i :: 0 <= i <= |s| - 3 ==> !(s[i] == s[i+2]))
}

predicate MinimalCUsage(s: string)
{
  forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b'
}

// <vc-helpers>
lemma LemmaVerifyNoForbiddenPattern(s: string, n: int)
  requires |s| == n
  requires forall i :: 0 <= i < n ==> s[i] == 'a' || s[i] == 'b' || s[i] == 'c'
  requires forall i :: 0 <= i < n - 2 ==> s[i] != s[i+2]
  ensures ValidOutput(s, n)
{
}

lemma LemmaMinimalCUsage(s: string)
  requires forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b'
  ensures MinimalCUsage(s)
{
}

lemma LemmaNoABCForbiddenPattern(s: seq<char>)
  requires forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b' || s[i] == 'c'
  requires forall i :: 0 <= i < |s| - 2 ==> s[i] != s[i+2]
  ensures ValidOutput(s, |s|)
{
}

lemma LemmaNoCRequired(s: seq<char>, i: int)
  requires 0 <= i <= n
  requires forall j :: 0 <= j < i ==> s[j] == 'a' || s[j] == 'b'
  requires forall j :: 0 <= j < i - 2 ==> s[j] != s[j+2]
  ensures forall j :: 0 <= j < i ==> s[j] == 'a' || s[j] == 'b'
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: string)
  requires ValidInput(n)
  ensures ValidOutput(result, n)
  ensures MinimalCUsage(result)
// </vc-spec>
// <vc-code>
{
  var s := new char[n];
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> s[j] == 'a' || s[j] == 'b'
    invariant forall j :: 0 <= j < i - 2 ==> s[j] != s[j+2]
  {
    if i == 0 {
      s[i] := 'a';
    } else if i == 1 {
      s[i] := 'b';
    } else {
      // Choose the next character to avoid s[i-2] == s[i]
      if s[i-2] == 'a' {
        s[i] := if s[i-1] == 'b' then 'a' else 'b';
      } else { // s[i-2] == 'b'
        s[i] := if s[i-1] == 'a' then 'b' else 'a';
      }
      
      assert s[i-2] != s[i];
    }
    i := i + 1;
  }
  
  result := s[0..n];
  LemmaMinimalCUsage(result);
  LemmaNoABCForbiddenPattern(s[0..n]);
}
// </vc-code>

