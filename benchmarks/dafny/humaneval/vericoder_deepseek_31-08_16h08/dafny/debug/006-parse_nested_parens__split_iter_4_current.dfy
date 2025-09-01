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
function max(a: int, b: int): int {
  if a > b then a else b
}

predicate balanced(s: string) {
  |s| > 0 && (forall i :: 0 <= i < |s| ==> s[i] == '(' || s[i] == ')') &&
  (var count := 0;
   var valid := true;
   forall i | 0 <= i < |s| 
     ensures count >= 0 && (i == |s| ==> count == 0)
   {
     if s[i] == '(' {
       count := count + 1;
     } else {
       count := count - 1;
     }
     valid := valid && count >= 0;
   } && count == 0 && valid)
}
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
  var start := 0;
  var i := 0;
  var current := "";
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= start <= i
    invariant |current| == i - start
    invariant forall j :: 0 <= j < |current| ==> current[j] == s[start + j]
    invariant forall j :: start <= j < i ==> s[j] != ' '
  {
    if s[i] == ' ' {
      if |current| > 0 {
        res := res + [current];
        current := "";
      }
      start := i + 1;
    } else {
      current := current + [s[i]];
    }
    i := i + 1;
  }
  
  if |current| > 0 {
    res := res + [current];
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