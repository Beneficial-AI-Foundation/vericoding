function Min(a: seq<int>) : int
  requires |a| > 0
{
  if |a| == 1 then a[0]
  else
    var minPrefix := Min(a[..|a|-1]);
    if a[|a|-1] <= minPrefix then a[|a|-1] else Min(a[..|a|-1])
}

//ATOM
function Max(a: seq<int>) : int
  requires |a| > 0
{
  if |a| == 1 then a[0]
  else
    var maxPrefix := Max(a[..|a|-1]);
    if a[|a|-1] >= maxPrefix then a[|a|-1] else Max(a[..|a|-1])
}

//IMPL
method SumMinMax(a: array<int>) returns (sum: int)
  requires a.Length > 0
  ensures sum == Max(a[..]) + Min(a[..])
{
  /* code modified by LLM (iteration 1): removed invalid text at beginning of file that was causing parse error */
  sum := Max(a[..]) + Min(a[..]);
}