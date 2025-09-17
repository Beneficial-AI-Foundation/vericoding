// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// ======= HELPERS =======
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method concatenate(strings: seq<string>) returns (result: string)
    ensures result == concat_strings(strings, 0)
    ensures |strings| == 0 ==> result == ""
// </vc-spec>
// <vc-code>
{
    result := "";
    for i := 0 to |strings|
        invariant result + concat_strings(strings, i) == concat_strings(strings, 0)
    {
        result := result + strings[i];
    }
}
// </vc-code>
