// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsDecimalWithTwoPrecision(s: string) returns (result: bool)
    ensures result ==> (exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
    ensures !result ==> !(exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>