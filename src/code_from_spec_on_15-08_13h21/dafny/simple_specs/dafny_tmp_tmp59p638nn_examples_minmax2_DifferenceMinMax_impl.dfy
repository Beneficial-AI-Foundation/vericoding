//ATOM

function Min(a: seq<int>) : (m: int)
  requires |a| > 0
{
  if |a| == 1 then a[0]
  else
   var minPrefix := Min(a[..|a|-1]);
   if a[|a|-1] <= minPrefix then a[|a|-1] else minPrefix
}


//ATOM

function Max(a: seq<int>) : (m: int)
  requires |a| > 0
{
  if |a| == 1 then a[0]
  else
   var maxPrefix := Max(a[..|a|-1]);
   if a[|a|-1] >= maxPrefix then a[|a|-1] else maxPrefix
}


//IMPL
method DifferenceMinMax(a: array<int>) returns (diff: int)
  requires a.Length > 0
  ensures diff == (Max(a[..]) - Min(a[..]))
{
  var maxVal := Max(a[..]);
  var minVal := Min(a[..]);
  diff := maxVal - minVal;
}