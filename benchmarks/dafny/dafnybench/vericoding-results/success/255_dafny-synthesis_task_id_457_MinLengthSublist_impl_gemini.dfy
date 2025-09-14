// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function FindMinSublist(s: seq<seq<int>>): (min: seq<int>)
  requires |s| > 0
  ensures min in s
  ensures forall sublist :: sublist in s ==> |min| <= |sublist|
{
  if |s| == 1 then
    s[0]
  else
    var tail_min := FindMinSublist(s[1..]);
    if |s[0]| <= |tail_min| then s[0] else tail_min
}
// </vc-helpers>

// <vc-spec>
method MinLengthSublist(s: seq<seq<int>>) returns (minSublist: seq<int>)
    requires |s| > 0
    ensures minSublist in s
    ensures forall sublist :: sublist in s ==> |minSublist| <= |sublist|
// </vc-spec>
// <vc-code>
{
  minSublist := FindMinSublist(s);
}
// </vc-code>
