// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function StrLen(s: string): nat { |s| }
// </vc-helpers>

// <vc-spec>
method strlen(s: string) returns (len: int)

  ensures len == |s|
// </vc-spec>
// <vc-code>
{
  len := |s|;
}
// </vc-code>
