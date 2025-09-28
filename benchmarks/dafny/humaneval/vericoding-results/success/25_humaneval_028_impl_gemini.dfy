// <vc-preamble>

function concat_strings(strings: seq<string>, index: nat): string
    requires index <= |strings|
    decreases |strings| - index
{
    if index == |strings| then ""
    else strings[index] + concat_strings(strings, index + 1)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method concatenate(strings: seq<string>) returns (result: string)
    ensures result == concat_strings(strings, 0)
    ensures |strings| == 0 ==> result == ""
// </vc-spec>
// <vc-code>
{
  result := "";
  var i: nat := 0;
  while i < |strings|
    invariant 0 <= i <= |strings|
    invariant result + concat_strings(strings, i) == concat_strings(strings, 0)
    decreases |strings| - i
  {
    result := result + strings[i];
    i := i + 1;
  }
}
// </vc-code>
