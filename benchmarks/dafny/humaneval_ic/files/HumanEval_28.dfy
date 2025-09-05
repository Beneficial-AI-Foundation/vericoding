This task involves implementing string concatenation. Given a sequence of strings, return a single string that is the concatenation of all strings in the list in order. The implementation should match the behavior of a recursive specification function.

// ======= TASK =======
// Given a list of strings, return a single string that is the concatenation 
// of all strings in the list in order.

// ======= SPEC REQUIREMENTS =======
function concat_strings(strings: seq<string>, index: nat): string
    requires index <= |strings|
    decreases |strings| - index
{
    if index == |strings| then ""
    else strings[index] + concat_strings(strings, index + 1)
}

// ======= HELPERS =======

// ======= MAIN METHOD =======
method concatenate(strings: seq<string>) returns (result: string)
    ensures result == concat_strings(strings, 0)
    ensures |strings| == 0 ==> result == ""
{
    result := "";
    for i := 0 to |strings|
        invariant result + concat_strings(strings, i) == concat_strings(strings, 0)
    {
        result := result + strings[i];
    }
}
