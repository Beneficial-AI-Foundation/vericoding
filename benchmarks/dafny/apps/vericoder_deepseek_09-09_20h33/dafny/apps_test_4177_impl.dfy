predicate ValidInput(s: string)
{
    |s| >= 1 && |s| <= 100 && forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

predicate ValidOutput(s: string, result: string)
{
    |result| == |s| && forall i :: 0 <= i < |result| ==> result[i] == 'x'
}

// <vc-helpers>
lemma StringLength(s: string)
  ensures |s| >= 0
{
}

lemma CharacterAccess(s: string, i: int)
  requires 0 <= i < |s|
{
}

function StringFromChars(chars: array<char>) : string
  requires chars != null
  reads chars
{
  var result: string := "";
  var i := 0;
  while i < chars.Length
    invariant 0 <= i <= chars.Length
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == chars[j]
  {
    result := result + [chars[i]];
    i := i + 1;
  }
  result
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidOutput(s, result)
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  var arr := new char[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant arr != null && arr.Length == n
    invariant forall j :: 0 <= j < i ==> arr[j] == 'x'
  {
    arr[i] := 'x';
    i := i + 1;
  }
  result := StringFromChars(arr);
}
// </vc-code>

