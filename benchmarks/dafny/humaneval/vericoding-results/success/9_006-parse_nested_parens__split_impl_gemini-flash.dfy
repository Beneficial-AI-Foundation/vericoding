// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function IsValidChar(c: char): bool { c == '(' || c == ')' }
// </vc-helpers>

// <vc-spec>
method split(s : string) returns (res : seq<string>)

    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')' || s[i] == ' '

    ensures forall s1 :: s1 in res ==> (forall i :: i >= 0 && i < |s1| ==> s1[i] == '(' || s1[i] == ')') && |s1| > 0
// </vc-spec>
// <vc-code>
{
  var tempRes: seq<string> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall s1 :: s1 in tempRes ==> (forall k :: 0 <= k < |s1| ==> IsValidChar(s1[k])) && |s1| > 0
  {
    if s[i] == ' ' {
      i := i + 1;
    } else {
      var j := i;
      while j < |s| && IsValidChar(s[j])
        invariant i <= j <= |s|
        invariant forall k :: i <= k < j ==> IsValidChar(s[k])
      {
        j := j + 1;
      }
      if j > i {
        tempRes := tempRes + [s[i..j]];
      }
      i := j;
    }
  }
  res := tempRes;
}
// </vc-code>
