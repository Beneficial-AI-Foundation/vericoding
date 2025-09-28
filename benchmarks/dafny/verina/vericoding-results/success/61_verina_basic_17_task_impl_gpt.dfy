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
/* helper modified by LLM (iteration 2): replaced invalid sequence comprehension with recursive definition */
function MapToLower(s: seq<char>): seq<char>
  ensures |MapToLower(s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> (if IsUppercase(s[i]) then MapToLower(s)[i] == Shift32(s[i]) else MapToLower(s)[i] == s[i])
  decreases |s|
{
  if |s| == 0 then
    []
  else
    [if IsUppercase(s[0]) then Shift32(s[0]) else s[0]] + MapToLower(s[1..])
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
  /* code modified by LLM (iteration 2): implement via helper MapToLower to satisfy postconditions */
  result := MapToLower(s);
}
// </vc-code>
