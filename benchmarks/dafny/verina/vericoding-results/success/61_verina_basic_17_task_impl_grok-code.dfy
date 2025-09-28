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
/* helper modified by LLM (iteration 2): No changes needed */
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
/* code modified by LLM (iteration 4): Fixed duplicate variable error by removing local 'var result' declaration and assigning directly to the out-parameter result, while preserving the loop logic to build the lowercase sequence. */
// impl-start
result := [];
var i: int := 0;
while i < |s|
  invariant 0 <= i <= |s|
  invariant |result| == i
  invariant forall k :: 0 <= k < i ==> if IsUppercase(s[k]) then result[k] == Shift32(s[k]) else result[k] == s[k]
{
  if IsUppercase(s[i]) {
    result := result + [Shift32(s[i])];
  } else {
    result := result + [s[i]];
  }
  i := i + 1;
}
// impl-end
}
// </vc-code>
