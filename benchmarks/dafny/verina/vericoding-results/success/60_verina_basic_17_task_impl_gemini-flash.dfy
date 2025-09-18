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
// No additional helpers are needed for this implementation.
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
  var res: seq<char> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> (if IsUppercase(s[j]) then res[j] == Shift32(s[j]) else res[j] == s[j])
  {
    if IsUppercase(s[i]) {
      res := res + [Shift32(s[i])];
    } else {
      res := res + [s[i]];
    }
    i := i + 1;
  }
  return res;
}
// </vc-code>
