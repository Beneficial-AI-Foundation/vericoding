// <vc-preamble>
predicate IsLowerCase(c: char)
{
    c >= 'a' && c <= 'z'
}

function ShiftMinus32Spec(c: char): char
    requires IsLowerCase(c)
{
    (c as int - 32) as char
}

function InnerExprToUppercase(str1: seq<char>, i: int): char
    requires 0 <= i < |str1|
{
    if IsLowerCase(str1[i]) then
        ShiftMinus32Spec(str1[i])
    else
        str1[i]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): char-level uppercase mapping */
function ToUpperChar(c: char): char
{
    if IsLowerCase(c) then ShiftMinus32Spec(c) else c
}
// </vc-helpers>

// <vc-spec>
method ToUppercase(str1: seq<char>) returns (result: seq<char>)
    ensures
        |str1| == |result| &&
        forall i :: 0 <= i < |str1| ==> result[i] == InnerExprToUppercase(str1, i)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): construct uppercase sequence via loop and invariants */
  var n := |str1|;
  var r: seq<char> := [];
  var i: int := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == InnerExprToUppercase(str1, j)
  {
    r := r + [InnerExprToUppercase(str1, i)];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
