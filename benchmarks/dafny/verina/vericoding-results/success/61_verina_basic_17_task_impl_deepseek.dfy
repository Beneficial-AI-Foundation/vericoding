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

function CharToLower(c: char): char
{
    if IsUppercase(c) then Shift32(c) else c
}

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
  /* code modified by LLM (iteration 2): fixed syntax error, replaced function method with function */
  result := [];
  var i := 0;
  while i < |s|
      invariant 0 <= i <= |s|
      invariant |result| == i
      invariant forall j :: 0 <= j < i ==> 
          if IsUppercase(s[j]) then
              result[j] == Shift32(s[j])
          else
              result[j] == s[j]
  {
      result := result + [CharToLower(s[i])];
      i := i + 1;
  }
}
// </vc-code>
