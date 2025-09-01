method parse_paren_group(s : string) returns (max_depth : int)
    // pre-conditions-start
    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')'
    // pre-conditions-end
    // post-conditions-start
    ensures max_depth >= 0
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method split(s : string) returns (res : seq<string>)
    // pre-conditions-start
    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')' || s[i] == ' '
    // pre-conditions-end
    // post-conditions-start
    ensures forall s1 :: s1 in res ==> (forall i :: i >= 0 && i < |s1| ==> s1[i] == '(' || s1[i] == ')') && |s1| > 0
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  res := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall t :: 0 <= t < |res| ==> (forall k :: 0 <= k < |res[t]| ==> res[t][k] == '(' || res[t][k] == ')') && |res[t]| > 0
    decreases |s| - i
  {
    if s[i] == ' ' {
      i := i + 1;
    } else {
      var j := i;
      while j < |s| && s[j] != ' '
        invariant i <= j <= |s|
        invariant forall k :: i <= k < j ==> s[k] != ' '
        decreases |s| - j
      {
        j := j + 1;
      }
      var token := s[i..j];
      assert |token| == j - i;
      assert |token| > 0;

      assert forall t :: 0 <= t < |token| ==> 0 <= i + t < |s|;
      assert forall t :: 0 <= t < |token| ==> i <= i + t < j;
      assert forall t :: 0 <= t < |token| ==> s[i + t] != ' ';
      assert forall t :: 0 <= t < |token| ==> token[t] == s[i + t];
      assert forall t :: 0 <= t < |token| ==> s[i + t] == '(' || s[i + t] == ')' || s[i + t] == ' ';
      assert forall t :: 0 <= t < |token| ==> token[t] == '(' || token[t] == ')';

      res := res + [token];
      i := j;
    }
  }
}
// </vc-code>

method parse_nested_parens(paren_string: string) returns (res : seq<int>)
    // pre-conditions-start
    requires forall i :: i >= 0 && i < |paren_string| ==> paren_string[i] == '(' || paren_string[i] == ')' || paren_string[i] == ' '
    // pre-conditions-end
    // post-conditions-start
    ensures forall x :: x in res ==> x >= 0
    // post-conditions-end
{
  assume{:axiom} false;
}