// <vc-preamble>
// Helper predicate to check if a character is uppercase
predicate IsUpperCase(c: char)
{
    'A' <= c <= 'Z'
}

// Helper predicate to check if a character is lowercase  
predicate IsLowerCase(c: char)
{
    'a' <= c <= 'z'
}

// Helper predicate to check if a character is alphabetic
predicate IsAlphabetic(c: char)
{
    IsUpperCase(c) || IsLowerCase(c)
}

// Helper function to convert a single character to lowercase
function ToLowerChar(c: char): char
{
    if IsUpperCase(c) then
        (c as int - 'A' as int + 'a' as int) as char
    else
        c
}

// Helper function to convert a string to lowercase
function ToLowerString(s: string): string
{
    seq(|s|, i requires 0 <= i < |s| => ToLowerChar(s[i]))
}

// Helper predicate to check if a string is already in lowercase
predicate IsLowerCaseString(s: string)
{
    forall i :: 0 <= i < |s| ==> !IsUpperCase(s[i])
}

/**
 * Converts each string element in the input sequence to lowercase.
 * Preserves sequence length and individual string lengths while applying
 * case transformation to alphabetic characters only.
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Lemma for ToLowerString on string concatenation. */
lemma {:auto} SuffixLower(s: string, c: char)
    ensures ToLowerString(s + [c]) == ToLowerString(s) + [ToLowerChar(c)]
{}

/* helper modified by LLM (iteration 2): Fixed loop verification issues. */
method LowerString(s: string) returns (res: string)
    ensures |res| == |s|
    ensures res == ToLowerString(s)
    ensures IsLowerCaseString(res)
{
    res := "";
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |res| == i
        invariant res == ToLowerString(s[..i])
        invariant IsLowerCaseString(res)
    {
        var next_char := ToLowerChar(s[i]);
        res := res + [next_char];
        i := i + 1;
    }
}
// </vc-helpers>

// <vc-spec>
method Lower(a: seq<string>) returns (result: seq<string>)
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == ToLowerString(a[i])
    ensures forall i :: 0 <= i < |a| ==> |result[i]| == |a[i]|
    ensures forall i :: 0 <= i < |a| ==> a[i] == "" ==> result[i] == ""
    ensures forall i :: 0 <= i < |a| ==> 
        forall j :: 0 <= j < |a[i]| ==> 
            result[i][j] == ToLowerChar(a[i][j])
    ensures forall i :: 0 <= i < |a| ==> IsLowerCaseString(result[i])
    ensures forall i :: 0 <= i < |a| ==> 
        forall j :: 0 <= j < |a[i]| ==> 
            !IsAlphabetic(a[i][j]) ==> result[i][j] == a[i][j]
    ensures forall i :: 0 <= i < |a| ==> 
        forall j :: 0 <= j < |a[i]| ==> 
            IsUpperCase(a[i][j]) ==> IsLowerCase(result[i][j])
    ensures forall i :: 0 <= i < |result| ==> ToLowerString(result[i]) == result[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Added explicit bounds invariant. */
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == ToLowerString(a[k])
  {
    var s_lower := LowerString(a[i]);
    result := result + [s_lower];
    i := i + 1;
  }
}
// </vc-code>
