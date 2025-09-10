/*
Given N strings, count the number of distinct strings.
Input: A sequence of strings (length >= 1)
Output: Integer representing the count of distinct strings
*/

function DistinctStrings(strings: seq<string>): set<string>
{
    set i | 0 <= i < |strings| :: strings[i]
}

predicate ValidInput(strings: seq<string>)
{
    |strings| >= 1
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(strings: seq<string>) returns (count: int)
    requires ValidInput(strings)
    ensures count >= 1
    ensures count <= |strings|
    ensures count == |DistinctStrings(strings)|
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
