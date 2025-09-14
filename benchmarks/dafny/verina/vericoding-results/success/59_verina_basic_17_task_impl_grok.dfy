// <vc-preamble>
/* Helper function to check if a character is uppercase */
predicate IsUppercase(c: char)
{
    'A' <= c <= 'Z'
}

/* Helper function to shift character by 32 positions */
function Shift32(c: char): char
    requires 'A' <= c <= 'Z'
{
    ((c as int) + 32) as char
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ToLowercase(s: seq<char>) returns (result: seq<char>)
    ensures
        |result| == |s| &&
        forall i :: 0 <= i < |s| ==> 
            if IsUppercase(s[i]) then
                result[i] == Shift32(s[i])
            else
                result[i] == s[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): added invariant idx <= |s| to resolve index out of range errors and prove postcondition */
  var res: seq<char> := [];
  var idx: nat := 0;
  while idx < |s|
    invariant |res| == idx
    invariant idx <= |s|
    invariant forall j :: 0 <= j < idx ==> res[j] == if IsUppercase(s[j]) then Shift32(s[j]) else s[j]
  {
    var c := if IsUppercase(s[idx]) then Shift32(s[idx]) else s[idx];
    res := res + [c];
    idx := idx + 1;
  }
  result := res;
}
// </vc-code>
