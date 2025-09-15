// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function strlenHelper(s: string, i: int): int
  requires 0 <= i <= |s|
  decreases |s| - i
  ensures strlenHelper(s, i) == |s| - i
{
  if i == |s| then
    0
  else
    1 + strlenHelper(s, i+1)
}
// </vc-helpers>

// <vc-spec>
method strlen(s: string) returns (len: int)

  ensures len == |s|
// </vc-spec>
// <vc-code>
{
  len := strlenHelper(s, 0);
}
// </vc-code>
