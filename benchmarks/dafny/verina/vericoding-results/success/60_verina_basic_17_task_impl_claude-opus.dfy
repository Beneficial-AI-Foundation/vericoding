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
  result := [];
  for i := 0 to |s|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==>
      if IsUppercase(s[j]) then
        result[j] == Shift32(s[j])
      else
        result[j] == s[j]
  {
    if IsUppercase(s[i]) {
      result := result + [Shift32(s[i])];
    } else {
      result := result + [s[i]];
    }
  }
}
// </vc-code>
