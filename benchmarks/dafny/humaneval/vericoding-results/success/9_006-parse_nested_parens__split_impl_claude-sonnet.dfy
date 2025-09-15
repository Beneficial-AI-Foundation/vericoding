// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method split(s : string) returns (res : seq<string>)

    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')' || s[i] == ' '

    ensures forall s1 :: s1 in res ==> (forall i :: i >= 0 && i < |s1| ==> s1[i] == '(' || s1[i] == ')') && |s1| > 0
// </vc-spec>
// <vc-code>
{
  res := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall s1 :: s1 in res ==> (forall j :: j >= 0 && j < |s1| ==> s1[j] == '(' || s1[j] == ')') && |s1| > 0
  {
    if s[i] == ' ' {
      i := i + 1;
    } else {
      var start := i;
      while i < |s| && s[i] != ' '
        invariant start <= i <= |s|
        invariant forall k :: start <= k < i ==> s[k] != ' '
      {
        i := i + 1;
      }
      if i > start {
        var token := s[start..i];
        res := res + [token];
      }
    }
  }
}
// </vc-code>
