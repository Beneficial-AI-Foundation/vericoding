// <vc-preamble>
// Helper predicate to check if a character is alphabetic (has upper/lower case variants)
predicate IsAlphabetic(c: char)
{
    ('a' <= c <= 'z') || ('A' <= c <= 'Z')
}

// Helper predicate to check if a character is lowercase
predicate IsLowercase(c: char)
{
    'a' <= c <= 'z'
}

// Helper predicate to check if a string satisfies the islower condition
predicate StringIsLower(s: string)
{
    // Has at least one cased character AND all cased characters are lowercase
    (exists i :: 0 <= i < |s| && IsAlphabetic(s[i]) && IsLowercase(s[i])) &&
    (forall i :: 0 <= i < |s| && IsAlphabetic(s[i]) ==> IsLowercase(s[i]))
}
// </vc-preamble>

// <vc-helpers>
method ComputeContainsLowercase(s: string) returns (res: bool)
  ensures res <==> (exists i :: 0 <= i < |s| && IsAlphabetic(s[i]) && IsLowercase(s[i]))
{
  res := false;
  var i := 0;
  while i < |s| && !res
    invariant 0 <= i <= |s|
    invariant res <==> (exists j :: 0 <= j < i && IsAlphabetic(s[j]) && IsLowercase(s[j]))
  {
    if IsAlphabetic(s[i]) && IsLowercase(s[i]) {
      res := true;
    }
    i := i + 1;
  }
}

method ComputeAllCasedAreLower(s: string) returns (res: bool)
  ensures res <==> (forall i :: 0 <= i < |s| && IsAlphabetic(s[i]) ==> IsLowercase(s[i]))
{
  res := true;
  var i := 0;
  while i < |s| && res
    invariant 0 <= i <= |s|
    invariant res <==> (forall j :: 0 <= j < i && IsAlphabetic(s[j]) ==> IsLowercase(s[j]))
  {
    if IsAlphabetic(s[i]) && !IsLowercase(s[i]) {
      res := false;
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method IsLower(a: seq<string>) returns (result: seq<bool>)
    requires |a| >= 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == StringIsLower(a[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed seq vs array type errors by using an intermediate array */
  var res_array := new bool[|a|];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < i ==> res_array[j] == StringIsLower(a[j])
  {
    var s := a[i];
    var contains_lowercase := ComputeContainsLowercase(s);
    var all_cased_are_lower := ComputeAllCasedAreLower(s);
    res_array[i] := contains_lowercase && all_cased_are_lower;
    i := i + 1;
  }
  result := res_array[..];
}
// </vc-code>
