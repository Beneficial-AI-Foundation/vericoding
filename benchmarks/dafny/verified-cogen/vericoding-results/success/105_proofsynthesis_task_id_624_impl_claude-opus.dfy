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

// </vc-helpers>

// <vc-spec>
method ToUppercase(str1: seq<char>) returns (result: seq<char>)
    ensures
        |str1| == |result| &&
        forall i :: 0 <= i < |str1| ==> result[i] == InnerExprToUppercase(str1, i)
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |str1|
    invariant 0 <= i <= |str1|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == InnerExprToUppercase(str1, j)
  {
    var c := str1[i];
    if IsLowerCase(c) {
      result := result + [ShiftMinus32Spec(c)];
    } else {
      result := result + [c];
    }
    i := i + 1;
  }
}
// </vc-code>
