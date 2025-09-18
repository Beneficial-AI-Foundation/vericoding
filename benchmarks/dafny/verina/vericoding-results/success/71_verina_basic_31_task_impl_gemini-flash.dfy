// <vc-preamble>
predicate IsLowerCase(c: char)
{
    'a' <= c && c <= 'z'
}

function ShiftMinus32(c: char): char
    requires 'a' <= c <= 'z'
{
    (c as int - 32) as char
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no issues, keeping correct output */
predicate IsUpperCase(c: char)
{
    'A' <= c && c <= 'Z'
}

function ToUpperChar(c: char): char
{
    if IsLowerCase(c) then
        ShiftMinus32(c)
    else
        c
}
// </vc-helpers>

// <vc-spec>
method ToUppercase(s: string) returns (result: string)
    ensures
        |result| == |s|
    ensures
        forall i :: 0 <= i < |s| ==> 
            var c := s[i];
            var r := result[i];
            if IsLowerCase(c) then
                r == ShiftMinus32(c)
            else
                r == c
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The compilation error `new can be applied only to class types (got string)` indicates that `new string(chars)` is not how to construct a string from a `char` array. The correct way to construct a string from a `char` array is to cast the array to `seq<char>` and then use the `string` constructor which takes `seq<char>`. This is done with `chars[..]` */
{
    var chars: array<char> := new char[|s|];
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant chars.Length == |s|
        invariant forall j :: 0 <= j < i ==> 
                      var c := s[j];
                      var r := chars[j];
                      if IsLowerCase(c) then
                          r == ShiftMinus32(c)
                      else
                          r == c
    {
        chars[i] := ToUpperChar(s[i]);
        i := i + 1;
    }
    result := chars[..]; // Correct way to convert array<char> to string
}
// </vc-code>
